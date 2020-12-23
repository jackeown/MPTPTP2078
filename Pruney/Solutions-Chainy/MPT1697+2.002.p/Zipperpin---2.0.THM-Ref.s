%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NTEpdYd8wC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:52 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  293 ( 996 expanded)
%              Number of leaves         :   48 ( 316 expanded)
%              Depth                    :   33
%              Number of atoms          : 4086 (37359 expanded)
%              Number of equality atoms :  161 (1275 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D_1 @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_F @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D_1 @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_F @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1 ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_F @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1 ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
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
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_F @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_subset_1 @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_subset_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D_1 ),
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
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
      ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('70',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_E @ sk_C_1 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_partfun1 @ sk_E @ sk_C_1 ),
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
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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
    v4_relat_1 @ sk_E @ sk_C_1 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C_1 ),
    inference(demod,[status(thm)],['80','83','86'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('88',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t68_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ A ) )
              & ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) ) )
           => ( B
              = ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X24
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X24 ) @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ X24 )
       != ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t68_funct_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('91',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('92',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('96',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('100',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['90','93','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( k1_xboole_0
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('105',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_E @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('108',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('110',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('111',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ( k1_xboole_0
       != ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['106','111'])).

thf('113',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','112'])).

thf('114',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('116',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('117',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 )
        = ( k7_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('123',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( v1_partfun1 @ X31 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D_1 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_F @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_F @ sk_D_1 ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_partfun1 @ sk_F @ sk_D_1 ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_partfun1 @ X35 @ X34 )
      | ( ( k1_relat_1 @ X35 )
        = X34 )
      | ~ ( v4_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('132',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('135',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('138',plain,(
    v4_relat_1 @ sk_F @ sk_D_1 ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D_1 ),
    inference(demod,[status(thm)],['132','135','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['90','93','100','101'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ sk_D_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_F )
      | ~ ( v1_funct_1 @ sk_F )
      | ( k1_xboole_0
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_F @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['133','134'])).

thf('143',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k3_xboole_0 @ sk_D_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_F @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ( k1_xboole_0
       != ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','146'])).

thf('148',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','114','115','116','121','148','149','150','151','152'])).

thf('154',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','154'])).

thf('156',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['157'])).

thf('159',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('160',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('161',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X24
        = ( k7_relat_1 @ X22 @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X24 ) @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ X24 )
       != ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t68_funct_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('165',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('166',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('174',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['157'])).

thf('175',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D_1 ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('177',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('178',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('179',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['172','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('182',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['171','182'])).

thf('184',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['133','134'])).

thf('186',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['170','186'])).

thf('188',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['81','82'])).

thf('190',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
    = ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('193',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('194',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('195',plain,(
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

thf('196',plain,(
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
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['194','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_2 @ sk_F @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('203',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('205',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D_1 )
      = ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('207',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('209',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['147'])).

thf('210',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['197','198','199','200','201','202','203','204','205','206','207','208','209','210','211','212','213'])).

thf('215',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['193','215'])).

thf('217',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
      = sk_F ) ),
    inference('sup-',[status(thm)],['192','217'])).

thf('219',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F ) ),
    inference(split,[status(esa)],['157'])).

thf('221',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
    = sk_F ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_D_1 )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) )
     != ( k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['157'])).

thf('232',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['191','230','231'])).

thf('233',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['158','232'])).

thf('234',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['156','233'])).

thf('235',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','234'])).

thf('236',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['0','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NTEpdYd8wC
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:25:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.49/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.73  % Solved by: fo/fo7.sh
% 0.49/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.73  % done 266 iterations in 0.262s
% 0.49/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.73  % SZS output start Refutation
% 0.49/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.49/0.73  thf(sk_F_type, type, sk_F: $i).
% 0.49/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.49/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.49/0.73  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.49/0.73  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.49/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.73  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.49/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.73  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.49/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.73  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.49/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.73  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.49/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.73  thf(sk_E_type, type, sk_E: $i).
% 0.49/0.73  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.49/0.73  thf(t6_tmap_1, conjecture,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.73       ( ![B:$i]:
% 0.49/0.73         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.73           ( ![C:$i]:
% 0.49/0.73             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.49/0.73                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.73               ( ![D:$i]:
% 0.49/0.73                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.49/0.73                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.73                   ( ( r1_subset_1 @ C @ D ) =>
% 0.49/0.73                     ( ![E:$i]:
% 0.49/0.73                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.49/0.73                           ( m1_subset_1 @
% 0.49/0.73                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.49/0.73                         ( ![F:$i]:
% 0.49/0.73                           ( ( ( v1_funct_1 @ F ) & 
% 0.49/0.73                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.49/0.73                               ( m1_subset_1 @
% 0.49/0.73                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.49/0.73                             ( ( ( k2_partfun1 @
% 0.49/0.73                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.49/0.73                                 ( k2_partfun1 @
% 0.49/0.73                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.49/0.73                               ( ( k2_partfun1 @
% 0.49/0.73                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.49/0.73                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.49/0.73                                 ( E ) ) & 
% 0.49/0.73                               ( ( k2_partfun1 @
% 0.49/0.73                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.49/0.73                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.49/0.73                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.73    (~( ![A:$i]:
% 0.49/0.73        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.73          ( ![B:$i]:
% 0.49/0.73            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.73              ( ![C:$i]:
% 0.49/0.73                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.49/0.73                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.73                  ( ![D:$i]:
% 0.49/0.73                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.49/0.73                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.73                      ( ( r1_subset_1 @ C @ D ) =>
% 0.49/0.73                        ( ![E:$i]:
% 0.49/0.73                          ( ( ( v1_funct_1 @ E ) & 
% 0.49/0.73                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.49/0.73                              ( m1_subset_1 @
% 0.49/0.73                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.49/0.73                            ( ![F:$i]:
% 0.49/0.73                              ( ( ( v1_funct_1 @ F ) & 
% 0.49/0.73                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.49/0.73                                  ( m1_subset_1 @
% 0.49/0.73                                    F @ 
% 0.49/0.73                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.49/0.73                                ( ( ( k2_partfun1 @
% 0.49/0.73                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.49/0.73                                    ( k2_partfun1 @
% 0.49/0.73                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.49/0.73                                  ( ( k2_partfun1 @
% 0.49/0.73                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.49/0.73                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.49/0.73                                    ( E ) ) & 
% 0.49/0.73                                  ( ( k2_partfun1 @
% 0.49/0.73                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.49/0.73                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.49/0.73                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.49/0.73    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.49/0.73  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('1', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('2', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('3', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(dt_k1_tmap_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.49/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.49/0.73         ( ~( v1_xboole_0 @ C ) ) & 
% 0.49/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.49/0.73         ( ~( v1_xboole_0 @ D ) ) & 
% 0.49/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.49/0.73         ( v1_funct_2 @ E @ C @ B ) & 
% 0.49/0.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.49/0.73         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.49/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.49/0.73       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.49/0.73         ( v1_funct_2 @
% 0.49/0.73           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.49/0.73           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.49/0.73         ( m1_subset_1 @
% 0.49/0.73           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.49/0.73           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.49/0.73  thf('4', plain,
% 0.49/0.73      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.49/0.73          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.49/0.73          | ~ (v1_funct_1 @ X47)
% 0.49/0.73          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.49/0.73          | (v1_xboole_0 @ X50)
% 0.49/0.73          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X51))
% 0.49/0.73          | (v1_xboole_0 @ X48)
% 0.49/0.73          | (v1_xboole_0 @ X49)
% 0.49/0.73          | (v1_xboole_0 @ X51)
% 0.49/0.73          | ~ (v1_funct_1 @ X52)
% 0.49/0.73          | ~ (v1_funct_2 @ X52 @ X50 @ X49)
% 0.49/0.73          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.49/0.73          | (v1_funct_1 @ (k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52)))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.49/0.73  thf('5', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.49/0.73          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | (v1_xboole_0 @ X2)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.49/0.73          | (v1_xboole_0 @ X1)
% 0.49/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.49/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.49/0.73          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.49/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.49/0.73  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('8', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.49/0.73          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | (v1_xboole_0 @ X2)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.49/0.73          | (v1_xboole_0 @ X1)
% 0.49/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.49/0.73      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.49/0.73  thf('9', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.49/0.73          | ~ (v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)
% 0.49/0.73          | (v1_funct_1 @ 
% 0.49/0.73             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['2', '8'])).
% 0.49/0.73  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('12', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | (v1_funct_1 @ 
% 0.49/0.73             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F)))),
% 0.49/0.73      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.49/0.73  thf('13', plain,
% 0.49/0.73      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.73        | (v1_xboole_0 @ sk_A)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['1', '12'])).
% 0.49/0.73  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('15', plain,
% 0.49/0.73      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.73        | (v1_xboole_0 @ sk_A)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.73  thf('16', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('17', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('18', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('19', plain,
% 0.49/0.73      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.49/0.73          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.49/0.73          | ~ (v1_funct_1 @ X47)
% 0.49/0.73          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.49/0.73          | (v1_xboole_0 @ X50)
% 0.49/0.73          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X51))
% 0.49/0.73          | (v1_xboole_0 @ X48)
% 0.49/0.73          | (v1_xboole_0 @ X49)
% 0.49/0.73          | (v1_xboole_0 @ X51)
% 0.49/0.73          | ~ (v1_funct_1 @ X52)
% 0.49/0.73          | ~ (v1_funct_2 @ X52 @ X50 @ X49)
% 0.49/0.73          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.49/0.73          | (v1_funct_2 @ (k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52) @ 
% 0.49/0.73             (k4_subset_1 @ X51 @ X48 @ X50) @ X49))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.49/0.73  thf('20', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.49/0.73           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.49/0.73          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.73          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.49/0.73          | ~ (v1_funct_1 @ X2)
% 0.49/0.73          | (v1_xboole_0 @ X1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.49/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.49/0.73          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.49/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.73  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('23', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.49/0.73           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.49/0.73          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.73          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.49/0.73          | ~ (v1_funct_1 @ X2)
% 0.49/0.73          | (v1_xboole_0 @ X1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.49/0.73  thf('24', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.49/0.73          | ~ (v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)
% 0.49/0.73          | (v1_funct_2 @ 
% 0.49/0.73             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1) @ sk_B))),
% 0.49/0.73      inference('sup-', [status(thm)], ['17', '23'])).
% 0.49/0.73  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('27', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | (v1_funct_2 @ 
% 0.49/0.73             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1) @ sk_B))),
% 0.49/0.73      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.49/0.73  thf('28', plain,
% 0.49/0.73      (((v1_funct_2 @ 
% 0.49/0.73         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_A)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['16', '27'])).
% 0.49/0.73  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('30', plain,
% 0.49/0.73      (((v1_funct_2 @ 
% 0.49/0.73         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_A)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['28', '29'])).
% 0.49/0.73  thf('31', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('32', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('33', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('34', plain,
% 0.49/0.73      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.49/0.73          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.49/0.73          | ~ (v1_funct_1 @ X47)
% 0.49/0.73          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.49/0.73          | (v1_xboole_0 @ X50)
% 0.49/0.73          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X51))
% 0.49/0.73          | (v1_xboole_0 @ X48)
% 0.49/0.73          | (v1_xboole_0 @ X49)
% 0.49/0.73          | (v1_xboole_0 @ X51)
% 0.49/0.73          | ~ (v1_funct_1 @ X52)
% 0.49/0.73          | ~ (v1_funct_2 @ X52 @ X50 @ X49)
% 0.49/0.73          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 0.49/0.73          | (m1_subset_1 @ (k1_tmap_1 @ X51 @ X49 @ X48 @ X50 @ X47 @ X52) @ 
% 0.49/0.73             (k1_zfmisc_1 @ 
% 0.49/0.73              (k2_zfmisc_1 @ (k4_subset_1 @ X51 @ X48 @ X50) @ X49))))),
% 0.49/0.73      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.49/0.73  thf('35', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.49/0.73           (k1_zfmisc_1 @ 
% 0.49/0.73            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.49/0.73          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.73          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.49/0.73          | ~ (v1_funct_1 @ X2)
% 0.49/0.73          | (v1_xboole_0 @ X1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.49/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.49/0.73          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.49/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.73  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('38', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.73         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.49/0.73           (k1_zfmisc_1 @ 
% 0.49/0.73            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.49/0.73          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.49/0.73          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.49/0.73          | ~ (v1_funct_1 @ X2)
% 0.49/0.73          | (v1_xboole_0 @ X1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.49/0.73      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.49/0.73  thf('39', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.49/0.73          | ~ (v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)
% 0.49/0.73          | (m1_subset_1 @ 
% 0.49/0.73             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73             (k1_zfmisc_1 @ 
% 0.49/0.73              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1) @ sk_B))))),
% 0.49/0.73      inference('sup-', [status(thm)], ['32', '38'])).
% 0.49/0.73  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('42', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.49/0.73          | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73          | (v1_xboole_0 @ sk_B)
% 0.49/0.73          | (v1_xboole_0 @ X0)
% 0.49/0.73          | (m1_subset_1 @ 
% 0.49/0.73             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73             (k1_zfmisc_1 @ 
% 0.49/0.73              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D_1) @ sk_B))))),
% 0.49/0.73      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.49/0.73  thf('43', plain,
% 0.49/0.73      (((m1_subset_1 @ 
% 0.49/0.73         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73         (k1_zfmisc_1 @ 
% 0.49/0.73          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)))
% 0.49/0.73        | (v1_xboole_0 @ sk_A)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['31', '42'])).
% 0.49/0.73  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('45', plain,
% 0.49/0.73      (((m1_subset_1 @ 
% 0.49/0.73         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73         (k1_zfmisc_1 @ 
% 0.49/0.73          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)))
% 0.49/0.73        | (v1_xboole_0 @ sk_A)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['43', '44'])).
% 0.49/0.73  thf(d1_tmap_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.73       ( ![B:$i]:
% 0.49/0.73         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.73           ( ![C:$i]:
% 0.49/0.73             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.49/0.73                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.73               ( ![D:$i]:
% 0.49/0.73                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.49/0.73                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.73                   ( ![E:$i]:
% 0.49/0.73                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.49/0.73                         ( m1_subset_1 @
% 0.49/0.73                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.49/0.73                       ( ![F:$i]:
% 0.49/0.73                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.49/0.73                             ( m1_subset_1 @
% 0.49/0.73                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.49/0.73                           ( ( ( k2_partfun1 @
% 0.49/0.73                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.49/0.73                               ( k2_partfun1 @
% 0.49/0.73                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.49/0.73                             ( ![G:$i]:
% 0.49/0.73                               ( ( ( v1_funct_1 @ G ) & 
% 0.49/0.73                                   ( v1_funct_2 @
% 0.49/0.73                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.49/0.73                                   ( m1_subset_1 @
% 0.49/0.73                                     G @ 
% 0.49/0.73                                     ( k1_zfmisc_1 @
% 0.49/0.73                                       ( k2_zfmisc_1 @
% 0.49/0.73                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.49/0.73                                 ( ( ( G ) =
% 0.49/0.73                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.49/0.73                                   ( ( ( k2_partfun1 @
% 0.49/0.73                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.49/0.73                                         C ) =
% 0.49/0.73                                       ( E ) ) & 
% 0.49/0.73                                     ( ( k2_partfun1 @
% 0.49/0.73                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.49/0.73                                         D ) =
% 0.49/0.73                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.73  thf('46', plain,
% 0.49/0.73      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.49/0.73         ((v1_xboole_0 @ X40)
% 0.49/0.73          | (v1_xboole_0 @ X41)
% 0.49/0.73          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.49/0.73          | ~ (v1_funct_1 @ X43)
% 0.49/0.73          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.49/0.73          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.49/0.73          | ((X46) != (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.49/0.73          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ X46 @ X45)
% 0.49/0.73              = (X44))
% 0.49/0.73          | ~ (m1_subset_1 @ X46 @ 
% 0.49/0.73               (k1_zfmisc_1 @ 
% 0.49/0.73                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.49/0.73          | ~ (v1_funct_2 @ X46 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.49/0.73          | ~ (v1_funct_1 @ X46)
% 0.49/0.73          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.49/0.73              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.49/0.73                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.49/0.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.49/0.73          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.49/0.73          | ~ (v1_funct_1 @ X44)
% 0.49/0.73          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.49/0.73          | (v1_xboole_0 @ X45)
% 0.49/0.73          | (v1_xboole_0 @ X42))),
% 0.49/0.73      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.49/0.73  thf('47', plain,
% 0.49/0.73      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.49/0.73         ((v1_xboole_0 @ X42)
% 0.49/0.73          | (v1_xboole_0 @ X45)
% 0.49/0.73          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.49/0.73          | ~ (v1_funct_1 @ X44)
% 0.49/0.73          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.49/0.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.49/0.73          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.49/0.73              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.49/0.73                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.49/0.73          | ~ (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.49/0.73          | ~ (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.49/0.73               (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.49/0.73          | ~ (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.49/0.73               (k1_zfmisc_1 @ 
% 0.49/0.73                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.49/0.73          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ 
% 0.49/0.73              (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ X45) = (
% 0.49/0.73              X44))
% 0.49/0.73          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.49/0.73          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.49/0.73          | ~ (v1_funct_1 @ X43)
% 0.49/0.73          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.49/0.73          | (v1_xboole_0 @ X41)
% 0.49/0.73          | (v1_xboole_0 @ X40))),
% 0.49/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.49/0.73  thf('48', plain,
% 0.49/0.73      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_A)
% 0.49/0.73        | (v1_xboole_0 @ sk_B)
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.73        | ~ (v1_funct_1 @ sk_F)
% 0.49/0.73        | ~ (v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)
% 0.49/0.73        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))
% 0.49/0.73        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.73            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.73            = (sk_E))
% 0.49/0.73        | ~ (v1_funct_2 @ 
% 0.49/0.73             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.73             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.73        | ~ (v1_funct_1 @ 
% 0.49/0.73             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.73        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.73            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.73            != (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.73                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))
% 0.49/0.73        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.49/0.73        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.49/0.73        | ~ (v1_funct_1 @ sk_E)
% 0.49/0.73        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_A))),
% 0.49/0.73      inference('sup-', [status(thm)], ['45', '47'])).
% 0.49/0.73  thf('49', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('52', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('53', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(redefinition_k9_subset_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.73       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.49/0.73  thf('54', plain,
% 0.49/0.73      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.49/0.73         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.49/0.73          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.49/0.73  thf('55', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         ((k9_subset_1 @ sk_A @ X0 @ sk_D_1) = (k3_xboole_0 @ X0 @ sk_D_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.73  thf('56', plain, ((r1_subset_1 @ sk_C_1 @ sk_D_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(redefinition_r1_subset_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.49/0.73       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.49/0.73  thf('57', plain,
% 0.49/0.73      (![X20 : $i, X21 : $i]:
% 0.49/0.73         ((v1_xboole_0 @ X20)
% 0.49/0.73          | (v1_xboole_0 @ X21)
% 0.49/0.73          | (r1_xboole_0 @ X20 @ X21)
% 0.49/0.73          | ~ (r1_subset_1 @ X20 @ X21))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.49/0.73  thf('58', plain,
% 0.49/0.73      (((r1_xboole_0 @ sk_C_1 @ sk_D_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.73        | (v1_xboole_0 @ sk_C_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['56', '57'])).
% 0.49/0.73  thf('59', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('60', plain,
% 0.49/0.73      (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D_1))),
% 0.49/0.73      inference('clc', [status(thm)], ['58', '59'])).
% 0.49/0.73  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('62', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D_1)),
% 0.49/0.73      inference('clc', [status(thm)], ['60', '61'])).
% 0.49/0.73  thf(d7_xboole_0, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.49/0.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.73  thf('63', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.49/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.49/0.73  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.73  thf('65', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(redefinition_k2_partfun1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.73     ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.73       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.49/0.73  thf('66', plain,
% 0.49/0.73      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.49/0.73          | ~ (v1_funct_1 @ X36)
% 0.49/0.73          | ((k2_partfun1 @ X37 @ X38 @ X36 @ X39) = (k7_relat_1 @ X36 @ X39)))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.49/0.73  thf('67', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ sk_E))),
% 0.49/0.73      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.73  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('69', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.49/0.73      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.73  thf(t2_boole, axiom,
% 0.49/0.73    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.73  thf('70', plain,
% 0.49/0.73      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.73  thf('71', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(cc5_funct_2, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.73       ( ![C:$i]:
% 0.49/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.73           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.49/0.73             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.49/0.73  thf('72', plain,
% 0.49/0.73      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.49/0.73          | (v1_partfun1 @ X31 @ X32)
% 0.49/0.73          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.49/0.73          | ~ (v1_funct_1 @ X31)
% 0.49/0.73          | (v1_xboole_0 @ X33))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.49/0.73  thf('73', plain,
% 0.49/0.73      (((v1_xboole_0 @ sk_B)
% 0.49/0.73        | ~ (v1_funct_1 @ sk_E)
% 0.49/0.73        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.49/0.73        | (v1_partfun1 @ sk_E @ sk_C_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['71', '72'])).
% 0.49/0.73  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('75', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('76', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_E @ sk_C_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.49/0.73  thf('77', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('78', plain, ((v1_partfun1 @ sk_E @ sk_C_1)),
% 0.49/0.73      inference('clc', [status(thm)], ['76', '77'])).
% 0.49/0.73  thf(d4_partfun1, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.49/0.73       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.49/0.73  thf('79', plain,
% 0.49/0.73      (![X34 : $i, X35 : $i]:
% 0.49/0.73         (~ (v1_partfun1 @ X35 @ X34)
% 0.49/0.73          | ((k1_relat_1 @ X35) = (X34))
% 0.49/0.73          | ~ (v4_relat_1 @ X35 @ X34)
% 0.49/0.73          | ~ (v1_relat_1 @ X35))),
% 0.49/0.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.73  thf('80', plain,
% 0.49/0.73      ((~ (v1_relat_1 @ sk_E)
% 0.49/0.73        | ~ (v4_relat_1 @ sk_E @ sk_C_1)
% 0.49/0.73        | ((k1_relat_1 @ sk_E) = (sk_C_1)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.73  thf('81', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(cc1_relset_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.73       ( v1_relat_1 @ C ) ))).
% 0.49/0.73  thf('82', plain,
% 0.49/0.73      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.73         ((v1_relat_1 @ X25)
% 0.49/0.73          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.73  thf('83', plain, ((v1_relat_1 @ sk_E)),
% 0.49/0.73      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.73  thf('84', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf(cc2_relset_1, axiom,
% 0.49/0.73    (![A:$i,B:$i,C:$i]:
% 0.49/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.49/0.73  thf('85', plain,
% 0.49/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.49/0.73         ((v4_relat_1 @ X28 @ X29)
% 0.49/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.73  thf('86', plain, ((v4_relat_1 @ sk_E @ sk_C_1)),
% 0.49/0.73      inference('sup-', [status(thm)], ['84', '85'])).
% 0.49/0.73  thf('87', plain, (((k1_relat_1 @ sk_E) = (sk_C_1))),
% 0.49/0.73      inference('demod', [status(thm)], ['80', '83', '86'])).
% 0.49/0.73  thf(t60_relat_1, axiom,
% 0.49/0.73    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.49/0.73     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.73  thf('88', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.73  thf(t68_funct_1, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.73       ( ![C:$i]:
% 0.49/0.73         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.73           ( ( ( ( k1_relat_1 @ B ) = ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ A ) ) & 
% 0.49/0.73               ( ![D:$i]:
% 0.49/0.73                 ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) =>
% 0.49/0.73                   ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 0.49/0.73             ( ( B ) = ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.49/0.73  thf('89', plain,
% 0.49/0.73      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.73         (~ (v1_relat_1 @ X22)
% 0.49/0.73          | ~ (v1_funct_1 @ X22)
% 0.49/0.73          | ((X24) = (k7_relat_1 @ X22 @ X23))
% 0.49/0.73          | (r2_hidden @ (sk_D @ X22 @ X24) @ (k1_relat_1 @ X24))
% 0.49/0.73          | ((k1_relat_1 @ X24) != (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23))
% 0.49/0.73          | ~ (v1_funct_1 @ X24)
% 0.49/0.73          | ~ (v1_relat_1 @ X24))),
% 0.49/0.73      inference('cnf', [status(esa)], [t68_funct_1])).
% 0.49/0.73  thf('90', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.49/0.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.73          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.49/0.73          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0))
% 0.49/0.73          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ X1)
% 0.49/0.73          | ~ (v1_relat_1 @ X1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['88', '89'])).
% 0.49/0.73  thf(t4_subset_1, axiom,
% 0.49/0.73    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.73  thf('91', plain,
% 0.49/0.73      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.49/0.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.73  thf('92', plain,
% 0.49/0.73      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.73         ((v1_relat_1 @ X25)
% 0.49/0.73          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.73  thf('93', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.73      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.73  thf('94', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('95', plain,
% 0.49/0.73      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.49/0.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.73  thf(cc3_funct_1, axiom,
% 0.49/0.73    (![A:$i]:
% 0.49/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.73       ( ![B:$i]:
% 0.49/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 0.49/0.73  thf('96', plain,
% 0.49/0.73      (![X18 : $i, X19 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.49/0.73          | (v1_funct_1 @ X18)
% 0.49/0.73          | ~ (v1_funct_1 @ X19)
% 0.49/0.73          | ~ (v1_relat_1 @ X19))),
% 0.49/0.73      inference('cnf', [status(esa)], [cc3_funct_1])).
% 0.49/0.73  thf('97', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (~ (v1_relat_1 @ X0)
% 0.49/0.73          | ~ (v1_funct_1 @ X0)
% 0.49/0.73          | (v1_funct_1 @ k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['95', '96'])).
% 0.49/0.73  thf('98', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_E))),
% 0.49/0.73      inference('sup-', [status(thm)], ['94', '97'])).
% 0.49/0.73  thf('99', plain, ((v1_relat_1 @ sk_E)),
% 0.49/0.73      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.73  thf('100', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.49/0.73      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.73  thf('101', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.73  thf('102', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.49/0.73          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0) @ k1_xboole_0)
% 0.49/0.73          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ X1)
% 0.49/0.73          | ~ (v1_relat_1 @ X1))),
% 0.49/0.73      inference('demod', [status(thm)], ['90', '93', '100', '101'])).
% 0.49/0.73  thf('103', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k3_xboole_0 @ sk_C_1 @ X0))
% 0.49/0.73          | ~ (v1_relat_1 @ sk_E)
% 0.49/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.49/0.73          | ((k1_xboole_0) = (k7_relat_1 @ sk_E @ X0))
% 0.49/0.73          | (r2_hidden @ (sk_D @ sk_E @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['87', '102'])).
% 0.49/0.73  thf('104', plain, ((v1_relat_1 @ sk_E)),
% 0.49/0.73      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.73  thf('105', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('106', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) != (k3_xboole_0 @ sk_C_1 @ X0))
% 0.49/0.73          | ((k1_xboole_0) = (k7_relat_1 @ sk_E @ X0))
% 0.49/0.73          | (r2_hidden @ (sk_D @ sk_E @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.73      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.49/0.73  thf('107', plain,
% 0.49/0.73      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.73  thf(t4_xboole_0, axiom,
% 0.49/0.73    (![A:$i,B:$i]:
% 0.49/0.73     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.73            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.49/0.73  thf('108', plain,
% 0.49/0.73      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.49/0.73         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.49/0.73          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.49/0.73      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.73  thf('109', plain,
% 0.49/0.73      (![X0 : $i, X1 : $i]:
% 0.49/0.73         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['107', '108'])).
% 0.49/0.73  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.49/0.73  thf('110', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.49/0.73      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.73  thf('111', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.49/0.73      inference('demod', [status(thm)], ['109', '110'])).
% 0.49/0.73  thf('112', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k1_xboole_0) = (k7_relat_1 @ sk_E @ X0))
% 0.49/0.73          | ((k1_xboole_0) != (k3_xboole_0 @ sk_C_1 @ X0)))),
% 0.49/0.73      inference('clc', [status(thm)], ['106', '111'])).
% 0.49/0.73  thf('113', plain,
% 0.49/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.73        | ((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0)))),
% 0.49/0.73      inference('sup-', [status(thm)], ['70', '112'])).
% 0.49/0.73  thf('114', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0))),
% 0.49/0.73      inference('simplify', [status(thm)], ['113'])).
% 0.49/0.73  thf('115', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         ((k9_subset_1 @ sk_A @ X0 @ sk_D_1) = (k3_xboole_0 @ X0 @ sk_D_1))),
% 0.49/0.73      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.73  thf('116', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.73  thf('117', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('118', plain,
% 0.49/0.73      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.49/0.73         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.49/0.73          | ~ (v1_funct_1 @ X36)
% 0.49/0.73          | ((k2_partfun1 @ X37 @ X38 @ X36 @ X39) = (k7_relat_1 @ X36 @ X39)))),
% 0.49/0.73      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.49/0.73  thf('119', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         (((k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.49/0.73          | ~ (v1_funct_1 @ sk_F))),
% 0.49/0.73      inference('sup-', [status(thm)], ['117', '118'])).
% 0.49/0.73  thf('120', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.73  thf('121', plain,
% 0.49/0.73      (![X0 : $i]:
% 0.49/0.73         ((k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.49/0.73      inference('demod', [status(thm)], ['119', '120'])).
% 0.49/0.73  thf('122', plain,
% 0.49/0.73      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.73      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.73  thf('123', plain,
% 0.49/0.73      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('124', plain,
% 0.49/0.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.49/0.74         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.49/0.74          | (v1_partfun1 @ X31 @ X32)
% 0.49/0.74          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.49/0.74          | ~ (v1_funct_1 @ X31)
% 0.49/0.74          | (v1_xboole_0 @ X33))),
% 0.49/0.74      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.49/0.74  thf('125', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_B)
% 0.49/0.74        | ~ (v1_funct_1 @ sk_F)
% 0.49/0.74        | ~ (v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)
% 0.49/0.74        | (v1_partfun1 @ sk_F @ sk_D_1))),
% 0.49/0.74      inference('sup-', [status(thm)], ['123', '124'])).
% 0.49/0.74  thf('126', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('127', plain, ((v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('128', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_F @ sk_D_1))),
% 0.49/0.74      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.49/0.74  thf('129', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('130', plain, ((v1_partfun1 @ sk_F @ sk_D_1)),
% 0.49/0.74      inference('clc', [status(thm)], ['128', '129'])).
% 0.49/0.74  thf('131', plain,
% 0.49/0.74      (![X34 : $i, X35 : $i]:
% 0.49/0.74         (~ (v1_partfun1 @ X35 @ X34)
% 0.49/0.74          | ((k1_relat_1 @ X35) = (X34))
% 0.49/0.74          | ~ (v4_relat_1 @ X35 @ X34)
% 0.49/0.74          | ~ (v1_relat_1 @ X35))),
% 0.49/0.74      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.74  thf('132', plain,
% 0.49/0.74      ((~ (v1_relat_1 @ sk_F)
% 0.49/0.74        | ~ (v4_relat_1 @ sk_F @ sk_D_1)
% 0.49/0.74        | ((k1_relat_1 @ sk_F) = (sk_D_1)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['130', '131'])).
% 0.49/0.74  thf('133', plain,
% 0.49/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('134', plain,
% 0.49/0.74      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.74         ((v1_relat_1 @ X25)
% 0.49/0.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.49/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.74  thf('135', plain, ((v1_relat_1 @ sk_F)),
% 0.49/0.74      inference('sup-', [status(thm)], ['133', '134'])).
% 0.49/0.74  thf('136', plain,
% 0.49/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('137', plain,
% 0.49/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.49/0.74         ((v4_relat_1 @ X28 @ X29)
% 0.49/0.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.49/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.74  thf('138', plain, ((v4_relat_1 @ sk_F @ sk_D_1)),
% 0.49/0.74      inference('sup-', [status(thm)], ['136', '137'])).
% 0.49/0.74  thf('139', plain, (((k1_relat_1 @ sk_F) = (sk_D_1))),
% 0.49/0.74      inference('demod', [status(thm)], ['132', '135', '138'])).
% 0.49/0.74  thf('140', plain,
% 0.49/0.74      (![X0 : $i, X1 : $i]:
% 0.49/0.74         (((k1_xboole_0) != (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.49/0.74          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0) @ k1_xboole_0)
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ X0))
% 0.49/0.74          | ~ (v1_funct_1 @ X1)
% 0.49/0.74          | ~ (v1_relat_1 @ X1))),
% 0.49/0.74      inference('demod', [status(thm)], ['90', '93', '100', '101'])).
% 0.49/0.74  thf('141', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (((k1_xboole_0) != (k3_xboole_0 @ sk_D_1 @ X0))
% 0.49/0.74          | ~ (v1_relat_1 @ sk_F)
% 0.49/0.74          | ~ (v1_funct_1 @ sk_F)
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ sk_F @ X0))
% 0.49/0.74          | (r2_hidden @ (sk_D @ sk_F @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['139', '140'])).
% 0.49/0.74  thf('142', plain, ((v1_relat_1 @ sk_F)),
% 0.49/0.74      inference('sup-', [status(thm)], ['133', '134'])).
% 0.49/0.74  thf('143', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('144', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (((k1_xboole_0) != (k3_xboole_0 @ sk_D_1 @ X0))
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ sk_F @ X0))
% 0.49/0.74          | (r2_hidden @ (sk_D @ sk_F @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.74      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.49/0.74  thf('145', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.49/0.74      inference('demod', [status(thm)], ['109', '110'])).
% 0.49/0.74  thf('146', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (((k1_xboole_0) = (k7_relat_1 @ sk_F @ X0))
% 0.49/0.74          | ((k1_xboole_0) != (k3_xboole_0 @ sk_D_1 @ X0)))),
% 0.49/0.74      inference('clc', [status(thm)], ['144', '145'])).
% 0.49/0.74  thf('147', plain,
% 0.49/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.74        | ((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['122', '146'])).
% 0.49/0.74  thf('148', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 0.49/0.74      inference('simplify', [status(thm)], ['147'])).
% 0.49/0.74  thf('149', plain,
% 0.49/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('150', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('151', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('152', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('153', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74            = (sk_E))
% 0.49/0.74        | ~ (v1_funct_2 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.74        | ~ (v1_funct_1 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | ((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_A))),
% 0.49/0.74      inference('demod', [status(thm)],
% 0.49/0.74                ['48', '49', '50', '51', '52', '55', '64', '69', '114', '115', 
% 0.49/0.74                 '116', '121', '148', '149', '150', '151', '152'])).
% 0.49/0.74  thf('154', plain,
% 0.49/0.74      ((~ (v1_funct_1 @ 
% 0.49/0.74           (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | ~ (v1_funct_2 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74            = (sk_E))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('simplify', [status(thm)], ['153'])).
% 0.49/0.74  thf('155', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74            = (sk_E))
% 0.49/0.74        | ~ (v1_funct_1 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['30', '154'])).
% 0.49/0.74  thf('156', plain,
% 0.49/0.74      ((~ (v1_funct_1 @ 
% 0.49/0.74           (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74            = (sk_E))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('simplify', [status(thm)], ['155'])).
% 0.49/0.74  thf('157', plain,
% 0.49/0.74      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74          != (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74            != (sk_E))
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74            != (sk_F)))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('158', plain,
% 0.49/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74          != (sk_E)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74                sk_C_1) = (sk_E))))),
% 0.49/0.74      inference('split', [status(esa)], ['157'])).
% 0.49/0.74  thf('159', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.74  thf('160', plain,
% 0.49/0.74      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.74  thf('161', plain,
% 0.49/0.74      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.74         (~ (v1_relat_1 @ X22)
% 0.49/0.74          | ~ (v1_funct_1 @ X22)
% 0.49/0.74          | ((X24) = (k7_relat_1 @ X22 @ X23))
% 0.49/0.74          | (r2_hidden @ (sk_D @ X22 @ X24) @ (k1_relat_1 @ X24))
% 0.49/0.74          | ((k1_relat_1 @ X24) != (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23))
% 0.49/0.74          | ~ (v1_funct_1 @ X24)
% 0.49/0.74          | ~ (v1_relat_1 @ X24))),
% 0.49/0.74      inference('cnf', [status(esa)], [t68_funct_1])).
% 0.49/0.74  thf('162', plain,
% 0.49/0.74      (![X0 : $i, X1 : $i]:
% 0.49/0.74         (((k1_relat_1 @ X1) != (k1_xboole_0))
% 0.49/0.74          | ~ (v1_relat_1 @ X1)
% 0.49/0.74          | ~ (v1_funct_1 @ X1)
% 0.49/0.74          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 0.49/0.74          | ((X1) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.74          | ~ (v1_funct_1 @ X0)
% 0.49/0.74          | ~ (v1_relat_1 @ X0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['160', '161'])).
% 0.49/0.74  thf('163', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.74          | ~ (v1_relat_1 @ X0)
% 0.49/0.74          | ~ (v1_funct_1 @ X0)
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.74          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0))
% 0.49/0.74          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.49/0.74          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['159', '162'])).
% 0.49/0.74  thf('164', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.74      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.74  thf('165', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.49/0.74      inference('demod', [status(thm)], ['98', '99'])).
% 0.49/0.74  thf('166', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.74      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.74  thf('167', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.74          | ~ (v1_relat_1 @ X0)
% 0.49/0.74          | ~ (v1_funct_1 @ X0)
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.74          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.74      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 0.49/0.74  thf('168', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.74          | ~ (v1_funct_1 @ X0)
% 0.49/0.74          | ~ (v1_relat_1 @ X0))),
% 0.49/0.74      inference('simplify', [status(thm)], ['167'])).
% 0.49/0.74  thf('169', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.49/0.74      inference('demod', [status(thm)], ['109', '110'])).
% 0.49/0.74  thf('170', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (~ (v1_relat_1 @ X0)
% 0.49/0.74          | ~ (v1_funct_1 @ X0)
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['168', '169'])).
% 0.49/0.74  thf('171', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (~ (v1_relat_1 @ X0)
% 0.49/0.74          | ~ (v1_funct_1 @ X0)
% 0.49/0.74          | ((k1_xboole_0) = (k7_relat_1 @ X0 @ k1_xboole_0)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['168', '169'])).
% 0.49/0.74  thf('172', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.49/0.74      inference('demod', [status(thm)], ['119', '120'])).
% 0.49/0.74  thf('173', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D_1) = (k3_xboole_0 @ X0 @ sk_D_1))),
% 0.49/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.74  thf('174', plain,
% 0.49/0.74      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74          != (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('split', [status(esa)], ['157'])).
% 0.49/0.74  thf('175', plain,
% 0.49/0.74      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74          != (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74              (k3_xboole_0 @ sk_C_1 @ sk_D_1))))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('sup-', [status(thm)], ['173', '174'])).
% 0.49/0.74  thf('176', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D_1) = (k3_xboole_0 @ X0 @ sk_D_1))),
% 0.49/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.74  thf('177', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.74  thf('178', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.74  thf('179', plain,
% 0.49/0.74      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0)
% 0.49/0.74          != (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ k1_xboole_0)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 0.49/0.74  thf('180', plain,
% 0.49/0.74      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ k1_xboole_0)
% 0.49/0.74          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('sup-', [status(thm)], ['172', '179'])).
% 0.49/0.74  thf('181', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.49/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.74  thf('182', plain,
% 0.49/0.74      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('demod', [status(thm)], ['180', '181'])).
% 0.49/0.74  thf('183', plain,
% 0.49/0.74      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.49/0.74         | ~ (v1_funct_1 @ sk_F)
% 0.49/0.74         | ~ (v1_relat_1 @ sk_F)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('sup-', [status(thm)], ['171', '182'])).
% 0.49/0.74  thf('184', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('185', plain, ((v1_relat_1 @ sk_F)),
% 0.49/0.74      inference('sup-', [status(thm)], ['133', '134'])).
% 0.49/0.74  thf('186', plain,
% 0.49/0.74      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.49/0.74  thf('187', plain,
% 0.49/0.74      (((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.74         | ~ (v1_funct_1 @ sk_E)
% 0.49/0.74         | ~ (v1_relat_1 @ sk_E)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('sup-', [status(thm)], ['170', '186'])).
% 0.49/0.74  thf('188', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('189', plain, ((v1_relat_1 @ sk_E)),
% 0.49/0.74      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.74  thf('190', plain,
% 0.49/0.74      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74                = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))))),
% 0.49/0.74      inference('demod', [status(thm)], ['187', '188', '189'])).
% 0.49/0.74  thf('191', plain,
% 0.49/0.74      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74          = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))))),
% 0.49/0.74      inference('simplify', [status(thm)], ['190'])).
% 0.49/0.74  thf('192', plain,
% 0.49/0.74      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.74  thf('193', plain,
% 0.49/0.74      (((v1_funct_2 @ 
% 0.49/0.74         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('demod', [status(thm)], ['28', '29'])).
% 0.49/0.74  thf('194', plain,
% 0.49/0.74      (((m1_subset_1 @ 
% 0.49/0.74         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74         (k1_zfmisc_1 @ 
% 0.49/0.74          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.49/0.74  thf('195', plain,
% 0.49/0.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.49/0.74         ((v1_xboole_0 @ X40)
% 0.49/0.74          | (v1_xboole_0 @ X41)
% 0.49/0.74          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.49/0.74          | ~ (v1_funct_1 @ X43)
% 0.49/0.74          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.49/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.49/0.74          | ((X46) != (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.49/0.74          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ X46 @ X41)
% 0.49/0.74              = (X43))
% 0.49/0.74          | ~ (m1_subset_1 @ X46 @ 
% 0.49/0.74               (k1_zfmisc_1 @ 
% 0.49/0.74                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.49/0.74          | ~ (v1_funct_2 @ X46 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.49/0.74          | ~ (v1_funct_1 @ X46)
% 0.49/0.74          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.49/0.74              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.49/0.74                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.49/0.74          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.49/0.74          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.49/0.74          | ~ (v1_funct_1 @ X44)
% 0.49/0.74          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.49/0.74          | (v1_xboole_0 @ X45)
% 0.49/0.74          | (v1_xboole_0 @ X42))),
% 0.49/0.74      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.49/0.74  thf('196', plain,
% 0.49/0.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.49/0.74         ((v1_xboole_0 @ X42)
% 0.49/0.74          | (v1_xboole_0 @ X45)
% 0.49/0.74          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X42))
% 0.49/0.74          | ~ (v1_funct_1 @ X44)
% 0.49/0.74          | ~ (v1_funct_2 @ X44 @ X45 @ X40)
% 0.49/0.74          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X40)))
% 0.49/0.74          | ((k2_partfun1 @ X45 @ X40 @ X44 @ (k9_subset_1 @ X42 @ X45 @ X41))
% 0.49/0.74              != (k2_partfun1 @ X41 @ X40 @ X43 @ 
% 0.49/0.74                  (k9_subset_1 @ X42 @ X45 @ X41)))
% 0.49/0.74          | ~ (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43))
% 0.49/0.74          | ~ (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.49/0.74               (k4_subset_1 @ X42 @ X45 @ X41) @ X40)
% 0.49/0.74          | ~ (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ 
% 0.49/0.74               (k1_zfmisc_1 @ 
% 0.49/0.74                (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40)))
% 0.49/0.74          | ((k2_partfun1 @ (k4_subset_1 @ X42 @ X45 @ X41) @ X40 @ 
% 0.49/0.74              (k1_tmap_1 @ X42 @ X40 @ X45 @ X41 @ X44 @ X43) @ X41) = (
% 0.49/0.74              X43))
% 0.49/0.74          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.49/0.74          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 0.49/0.74          | ~ (v1_funct_1 @ X43)
% 0.49/0.74          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 0.49/0.74          | (v1_xboole_0 @ X41)
% 0.49/0.74          | (v1_xboole_0 @ X40))),
% 0.49/0.74      inference('simplify', [status(thm)], ['195'])).
% 0.49/0.74  thf('197', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.74        | ~ (v1_funct_1 @ sk_F)
% 0.49/0.74        | ~ (v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)
% 0.49/0.74        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74            = (sk_F))
% 0.49/0.74        | ~ (v1_funct_2 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.74        | ~ (v1_funct_1 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74            != (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1)))
% 0.49/0.74        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.49/0.74        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.49/0.74        | ~ (v1_funct_1 @ sk_E)
% 0.49/0.74        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_A))),
% 0.49/0.74      inference('sup-', [status(thm)], ['194', '196'])).
% 0.49/0.74  thf('198', plain, ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('199', plain, ((v1_funct_1 @ sk_F)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('200', plain, ((v1_funct_2 @ sk_F @ sk_D_1 @ sk_B)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('201', plain,
% 0.49/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D_1 @ sk_B)))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('202', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D_1) = (k3_xboole_0 @ X0 @ sk_D_1))),
% 0.49/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.74  thf('203', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.74  thf('204', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.49/0.74      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.74  thf('205', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ k1_xboole_0))),
% 0.49/0.74      inference('simplify', [status(thm)], ['113'])).
% 0.49/0.74  thf('206', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k9_subset_1 @ sk_A @ X0 @ sk_D_1) = (k3_xboole_0 @ X0 @ sk_D_1))),
% 0.49/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.74  thf('207', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.49/0.74  thf('208', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         ((k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.49/0.74      inference('demod', [status(thm)], ['119', '120'])).
% 0.49/0.74  thf('209', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_F @ k1_xboole_0))),
% 0.49/0.74      inference('simplify', [status(thm)], ['147'])).
% 0.49/0.74  thf('210', plain,
% 0.49/0.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('211', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('212', plain, ((v1_funct_1 @ sk_E)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('213', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('214', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74            = (sk_F))
% 0.49/0.74        | ~ (v1_funct_2 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.74        | ~ (v1_funct_1 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | ((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_A))),
% 0.49/0.74      inference('demod', [status(thm)],
% 0.49/0.74                ['197', '198', '199', '200', '201', '202', '203', '204', 
% 0.49/0.74                 '205', '206', '207', '208', '209', '210', '211', '212', '213'])).
% 0.49/0.74  thf('215', plain,
% 0.49/0.74      ((~ (v1_funct_1 @ 
% 0.49/0.74           (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | ~ (v1_funct_2 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B)
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74            = (sk_F))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('simplify', [status(thm)], ['214'])).
% 0.49/0.74  thf('216', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74            = (sk_F))
% 0.49/0.74        | ~ (v1_funct_1 @ 
% 0.49/0.74             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['193', '215'])).
% 0.49/0.74  thf('217', plain,
% 0.49/0.74      ((~ (v1_funct_1 @ 
% 0.49/0.74           (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74            = (sk_F))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('simplify', [status(thm)], ['216'])).
% 0.49/0.74  thf('218', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74            = (sk_F)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['192', '217'])).
% 0.49/0.74  thf('219', plain,
% 0.49/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74          = (sk_F))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('simplify', [status(thm)], ['218'])).
% 0.49/0.74  thf('220', plain,
% 0.49/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74          != (sk_F)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74                sk_D_1) = (sk_F))))),
% 0.49/0.74      inference('split', [status(esa)], ['157'])).
% 0.49/0.74  thf('221', plain,
% 0.49/0.74      (((((sk_F) != (sk_F))
% 0.49/0.74         | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74         | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74         | (v1_xboole_0 @ sk_B)
% 0.49/0.74         | (v1_xboole_0 @ sk_A)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74                sk_D_1) = (sk_F))))),
% 0.49/0.74      inference('sup-', [status(thm)], ['219', '220'])).
% 0.49/0.74  thf('222', plain,
% 0.49/0.74      ((((v1_xboole_0 @ sk_A)
% 0.49/0.74         | (v1_xboole_0 @ sk_B)
% 0.49/0.74         | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74         | (v1_xboole_0 @ sk_D_1)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74                sk_D_1) = (sk_F))))),
% 0.49/0.74      inference('simplify', [status(thm)], ['221'])).
% 0.49/0.74  thf('223', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('224', plain,
% 0.49/0.74      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74                sk_D_1) = (sk_F))))),
% 0.49/0.74      inference('sup-', [status(thm)], ['222', '223'])).
% 0.49/0.74  thf('225', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('226', plain,
% 0.49/0.74      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74                sk_D_1) = (sk_F))))),
% 0.49/0.74      inference('clc', [status(thm)], ['224', '225'])).
% 0.49/0.74  thf('227', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('228', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_B))
% 0.49/0.74         <= (~
% 0.49/0.74             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ 
% 0.49/0.74                sk_D_1) = (sk_F))))),
% 0.49/0.74      inference('clc', [status(thm)], ['226', '227'])).
% 0.49/0.74  thf('229', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('230', plain,
% 0.49/0.74      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74          = (sk_F)))),
% 0.49/0.74      inference('sup-', [status(thm)], ['228', '229'])).
% 0.49/0.74  thf('231', plain,
% 0.49/0.74      (~
% 0.49/0.74       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74          = (sk_E))) | 
% 0.49/0.74       ~
% 0.49/0.74       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_D_1)
% 0.49/0.74          = (sk_F))) | 
% 0.49/0.74       ~
% 0.49/0.74       (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.49/0.74          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))
% 0.49/0.74          = (k2_partfun1 @ sk_D_1 @ sk_B @ sk_F @ 
% 0.49/0.74             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D_1))))),
% 0.49/0.74      inference('split', [status(esa)], ['157'])).
% 0.49/0.74  thf('232', plain,
% 0.49/0.74      (~
% 0.49/0.74       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74          = (sk_E)))),
% 0.49/0.74      inference('sat_resolution*', [status(thm)], ['191', '230', '231'])).
% 0.49/0.74  thf('233', plain,
% 0.49/0.74      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D_1) @ sk_B @ 
% 0.49/0.74         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F) @ sk_C_1)
% 0.49/0.74         != (sk_E))),
% 0.49/0.74      inference('simpl_trail', [status(thm)], ['158', '232'])).
% 0.49/0.74  thf('234', plain,
% 0.49/0.74      ((~ (v1_funct_1 @ 
% 0.49/0.74           (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_E @ sk_F))
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('simplify_reflect-', [status(thm)], ['156', '233'])).
% 0.49/0.74  thf('235', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_A))),
% 0.49/0.74      inference('sup-', [status(thm)], ['15', '234'])).
% 0.49/0.74  thf('236', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_A)
% 0.49/0.74        | (v1_xboole_0 @ sk_B)
% 0.49/0.74        | (v1_xboole_0 @ sk_C_1)
% 0.49/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.49/0.74      inference('simplify', [status(thm)], ['235'])).
% 0.49/0.74  thf('237', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('238', plain,
% 0.49/0.74      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.49/0.74      inference('sup-', [status(thm)], ['236', '237'])).
% 0.49/0.74  thf('239', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('240', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.49/0.74      inference('clc', [status(thm)], ['238', '239'])).
% 0.49/0.74  thf('241', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('242', plain, ((v1_xboole_0 @ sk_B)),
% 0.49/0.74      inference('clc', [status(thm)], ['240', '241'])).
% 0.49/0.74  thf('243', plain, ($false), inference('demod', [status(thm)], ['0', '242'])).
% 0.49/0.74  
% 0.49/0.74  % SZS output end Refutation
% 0.49/0.74  
% 0.49/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
