%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RJvPsn2GLD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:11 EST 2020

% Result     : Theorem 3.40s
% Output     : Refutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :  302 (2710 expanded)
%              Number of leaves         :   35 ( 796 expanded)
%              Depth                    :   35
%              Number of atoms          : 4743 (116305 expanded)
%              Number of equality atoms :   54 (1715 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t139_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( A
                      = ( k1_tsep_1 @ A @ C @ D ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( A
                        = ( k1_tsep_1 @ A @ C @ D ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r1_funct_2 @ X6 @ X7 @ X8 @ X9 @ X10 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X0 @ sk_E @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X0 @ sk_E @ sk_E ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('15',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X19 )
      | ( ( k3_tmap_1 @ X18 @ X16 @ X19 @ X17 @ X20 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) @ X20 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( ( k2_tmap_1 @ X14 @ X12 @ X15 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X15 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['54','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63','64'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','94'])).

thf(dt_k10_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
        & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['100','114'])).

thf('116',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','121'])).

thf('123',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('125',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['124','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','137'])).

thf('139',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('140',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['122','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['72','145'])).

thf('147',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('149',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['54','70'])).

thf('151',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('158',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['54','70'])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['146','155','164'])).

thf('166',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','165'])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','71'])).

thf('173',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','94'])).

thf('174',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X25 @ X22 @ X24 ) ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('180',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['172','181'])).

thf('183',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('184',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['171','185'])).

thf('187',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['186','187','188','189','190'])).

thf('192',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t138_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) )).

thf('194',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ X34 @ X35 @ X33 ) ) @ ( u1_struct_0 @ X32 ) @ X36 @ ( k10_tmap_1 @ X34 @ X32 @ X35 @ X33 @ ( k3_tmap_1 @ X34 @ X32 @ ( k1_tsep_1 @ X34 @ X35 @ X33 ) @ X35 @ X36 ) @ ( k3_tmap_1 @ X34 @ X32 @ ( k1_tsep_1 @ X34 @ X35 @ X33 ) @ X33 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X34 @ X35 @ X33 ) ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ ( k1_tsep_1 @ X34 @ X35 @ X33 ) ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t138_tmap_1])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ X1 ) @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1 ) @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['195','196','197','198','199','200','201','202','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['192','204'])).

thf('206',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('209',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['54','70'])).

thf('210',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['205','206','207','208','209','210','211'])).

thf('213',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','71'])).

thf('215',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','94'])).

thf('216',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X25 @ X22 @ X24 ) ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('217',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('222',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('223',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['214','223'])).

thf('225',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('226',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['213','227'])).

thf('229',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['228','229','230','231','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['233','239'])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['212','240'])).

thf('242',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['191','242'])).

thf('244',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['170','244'])).

thf('246',plain,
    ( ( sk_E
      = ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['246','249'])).

thf('251',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','250'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('252',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('253',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('255',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('256',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['253','256'])).

thf('258',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['262','263'])).

thf('265',plain,(
    $false ),
    inference(demod,[status(thm)],['0','264'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RJvPsn2GLD
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % DateTime   : Tue Dec  1 11:15:56 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 3.40/3.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.40/3.62  % Solved by: fo/fo7.sh
% 3.40/3.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.40/3.62  % done 2876 iterations in 3.171s
% 3.40/3.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.40/3.62  % SZS output start Refutation
% 3.40/3.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.40/3.62  thf(sk_E_type, type, sk_E: $i).
% 3.40/3.62  thf(sk_A_type, type, sk_A: $i).
% 3.40/3.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.40/3.62  thf(sk_C_type, type, sk_C: $i).
% 3.40/3.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.40/3.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.40/3.62  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 3.40/3.62  thf(sk_D_type, type, sk_D: $i).
% 3.40/3.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 3.40/3.62  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 3.40/3.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 3.40/3.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.40/3.62  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 3.40/3.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.40/3.62  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 3.40/3.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 3.40/3.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.40/3.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.40/3.62  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 3.40/3.62  thf(sk_B_type, type, sk_B: $i).
% 3.40/3.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.40/3.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.40/3.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.40/3.62  thf(t139_tmap_1, conjecture,
% 3.40/3.62    (![A:$i]:
% 3.40/3.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.40/3.62       ( ![B:$i]:
% 3.40/3.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.40/3.62             ( l1_pre_topc @ B ) ) =>
% 3.40/3.62           ( ![C:$i]:
% 3.40/3.62             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.40/3.62               ( ![D:$i]:
% 3.40/3.62                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.40/3.62                   ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 3.40/3.62                     ( ![E:$i]:
% 3.40/3.62                       ( ( ( v1_funct_1 @ E ) & 
% 3.40/3.62                           ( v1_funct_2 @
% 3.40/3.62                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62                           ( m1_subset_1 @
% 3.40/3.62                             E @ 
% 3.40/3.62                             ( k1_zfmisc_1 @
% 3.40/3.62                               ( k2_zfmisc_1 @
% 3.40/3.62                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.40/3.62                         ( r1_funct_2 @
% 3.40/3.62                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.40/3.62                           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 3.40/3.62                           ( u1_struct_0 @ B ) @ E @ 
% 3.40/3.62                           ( k10_tmap_1 @
% 3.40/3.62                             A @ B @ C @ D @ ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 3.40/3.62                             ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.40/3.62  thf(zf_stmt_0, negated_conjecture,
% 3.40/3.62    (~( ![A:$i]:
% 3.40/3.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.40/3.62            ( l1_pre_topc @ A ) ) =>
% 3.40/3.62          ( ![B:$i]:
% 3.40/3.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.40/3.62                ( l1_pre_topc @ B ) ) =>
% 3.40/3.62              ( ![C:$i]:
% 3.40/3.62                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.40/3.62                  ( ![D:$i]:
% 3.40/3.62                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.40/3.62                      ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 3.40/3.62                        ( ![E:$i]:
% 3.40/3.62                          ( ( ( v1_funct_1 @ E ) & 
% 3.40/3.62                              ( v1_funct_2 @
% 3.40/3.62                                E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62                              ( m1_subset_1 @
% 3.40/3.62                                E @ 
% 3.40/3.62                                ( k1_zfmisc_1 @
% 3.40/3.62                                  ( k2_zfmisc_1 @
% 3.40/3.62                                    ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.40/3.62                            ( r1_funct_2 @
% 3.40/3.62                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 3.40/3.62                              ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 3.40/3.62                              ( u1_struct_0 @ B ) @ E @ 
% 3.40/3.62                              ( k10_tmap_1 @
% 3.40/3.62                                A @ B @ C @ D @ 
% 3.40/3.62                                ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 3.40/3.62                                ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.40/3.62    inference('cnf.neg', [status(esa)], [t139_tmap_1])).
% 3.40/3.62  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('1', plain,
% 3.40/3.62      ((m1_subset_1 @ sk_E @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('2', plain,
% 3.40/3.62      ((m1_subset_1 @ sk_E @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf(reflexivity_r1_funct_2, axiom,
% 3.40/3.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.40/3.62     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 3.40/3.62         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 3.40/3.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.40/3.62         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 3.40/3.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.40/3.62       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 3.40/3.62  thf('3', plain,
% 3.40/3.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 3.40/3.62         ((r1_funct_2 @ X6 @ X7 @ X8 @ X9 @ X10 @ X10)
% 3.40/3.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 3.40/3.62          | ~ (v1_funct_2 @ X10 @ X6 @ X7)
% 3.40/3.62          | ~ (v1_funct_1 @ X10)
% 3.40/3.62          | (v1_xboole_0 @ X9)
% 3.40/3.62          | (v1_xboole_0 @ X7)
% 3.40/3.62          | ~ (v1_funct_1 @ X11)
% 3.40/3.62          | ~ (v1_funct_2 @ X11 @ X8 @ X9)
% 3.40/3.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.40/3.62      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 3.40/3.62  thf('4', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.62         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.40/3.62          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 3.40/3.62          | ~ (v1_funct_1 @ X2)
% 3.40/3.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | (v1_xboole_0 @ X0)
% 3.40/3.62          | ~ (v1_funct_1 @ sk_E)
% 3.40/3.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 3.40/3.62             X0 @ sk_E @ sk_E))),
% 3.40/3.62      inference('sup-', [status(thm)], ['2', '3'])).
% 3.40/3.62  thf('5', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('6', plain,
% 3.40/3.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('7', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.62         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.40/3.62          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 3.40/3.62          | ~ (v1_funct_1 @ X2)
% 3.40/3.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | (v1_xboole_0 @ X0)
% 3.40/3.62          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 3.40/3.62             X0 @ sk_E @ sk_E))),
% 3.40/3.62      inference('demod', [status(thm)], ['4', '5', '6'])).
% 3.40/3.62  thf('8', plain,
% 3.40/3.62      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 3.40/3.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 3.40/3.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 3.40/3.62        | ~ (v1_funct_1 @ sk_E)
% 3.40/3.62        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.62      inference('sup-', [status(thm)], ['1', '7'])).
% 3.40/3.62  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('10', plain,
% 3.40/3.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('11', plain,
% 3.40/3.62      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 3.40/3.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 3.40/3.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 3.40/3.62      inference('demod', [status(thm)], ['8', '9', '10'])).
% 3.40/3.62  thf('12', plain,
% 3.40/3.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 3.40/3.62        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E))),
% 3.40/3.62      inference('simplify', [status(thm)], ['11'])).
% 3.40/3.62  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf(t2_tsep_1, axiom,
% 3.40/3.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 3.40/3.62  thf('15', plain,
% 3.40/3.62      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 3.40/3.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.40/3.62  thf('16', plain,
% 3.40/3.62      ((m1_subset_1 @ sk_E @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf(dt_k3_tmap_1, axiom,
% 3.40/3.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.40/3.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.40/3.62         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 3.40/3.62         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 3.40/3.62         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 3.40/3.62         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62         ( m1_subset_1 @
% 3.40/3.62           E @ 
% 3.40/3.62           ( k1_zfmisc_1 @
% 3.40/3.62             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.40/3.62       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 3.40/3.62         ( v1_funct_2 @
% 3.40/3.62           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 3.40/3.62           ( u1_struct_0 @ B ) ) & 
% 3.40/3.62         ( m1_subset_1 @
% 3.40/3.62           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 3.40/3.62           ( k1_zfmisc_1 @
% 3.40/3.62             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 3.40/3.62  thf('17', plain,
% 3.40/3.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ X27 @ X28)
% 3.40/3.62          | ~ (m1_pre_topc @ X29 @ X28)
% 3.40/3.62          | ~ (l1_pre_topc @ X30)
% 3.40/3.62          | ~ (v2_pre_topc @ X30)
% 3.40/3.62          | (v2_struct_0 @ X30)
% 3.40/3.62          | ~ (l1_pre_topc @ X28)
% 3.40/3.62          | ~ (v2_pre_topc @ X28)
% 3.40/3.62          | (v2_struct_0 @ X28)
% 3.40/3.62          | ~ (v1_funct_1 @ X31)
% 3.40/3.62          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 3.40/3.62          | ~ (m1_subset_1 @ X31 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 3.40/3.62          | (m1_subset_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 3.40/3.62             (k1_zfmisc_1 @ 
% 3.40/3.62              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))))),
% 3.40/3.62      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 3.40/3.62  thf('18', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62           (k1_zfmisc_1 @ 
% 3.40/3.62            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ~ (v1_funct_1 @ sk_E)
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (v2_pre_topc @ X1)
% 3.40/3.62          | ~ (l1_pre_topc @ X1)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.62      inference('sup-', [status(thm)], ['16', '17'])).
% 3.40/3.62  thf('19', plain,
% 3.40/3.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('20', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('23', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62           (k1_zfmisc_1 @ 
% 3.40/3.62            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (v2_pre_topc @ X1)
% 3.40/3.62          | ~ (l1_pre_topc @ X1)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.62      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 3.40/3.62  thf('24', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_A)
% 3.40/3.62          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62             (k1_zfmisc_1 @ 
% 3.40/3.62              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 3.40/3.62      inference('sup-', [status(thm)], ['15', '23'])).
% 3.40/3.62  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('28', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_A)
% 3.40/3.62          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62             (k1_zfmisc_1 @ 
% 3.40/3.62              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 3.40/3.62      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 3.40/3.62  thf('29', plain,
% 3.40/3.62      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 3.40/3.62         (k1_zfmisc_1 @ 
% 3.40/3.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 3.40/3.62        | (v2_struct_0 @ sk_A)
% 3.40/3.62        | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('sup-', [status(thm)], ['14', '28'])).
% 3.40/3.62  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('31', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 3.40/3.62           (k1_zfmisc_1 @ 
% 3.40/3.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 3.40/3.62      inference('clc', [status(thm)], ['29', '30'])).
% 3.40/3.62  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('33', plain,
% 3.40/3.62      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('clc', [status(thm)], ['31', '32'])).
% 3.40/3.62  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('35', plain,
% 3.40/3.62      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 3.40/3.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.40/3.62  thf('36', plain,
% 3.40/3.62      ((m1_subset_1 @ sk_E @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf(d5_tmap_1, axiom,
% 3.40/3.62    (![A:$i]:
% 3.40/3.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.40/3.62       ( ![B:$i]:
% 3.40/3.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.40/3.62             ( l1_pre_topc @ B ) ) =>
% 3.40/3.62           ( ![C:$i]:
% 3.40/3.62             ( ( m1_pre_topc @ C @ A ) =>
% 3.40/3.62               ( ![D:$i]:
% 3.40/3.62                 ( ( m1_pre_topc @ D @ A ) =>
% 3.40/3.62                   ( ![E:$i]:
% 3.40/3.62                     ( ( ( v1_funct_1 @ E ) & 
% 3.40/3.62                         ( v1_funct_2 @
% 3.40/3.62                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62                         ( m1_subset_1 @
% 3.40/3.62                           E @ 
% 3.40/3.62                           ( k1_zfmisc_1 @
% 3.40/3.62                             ( k2_zfmisc_1 @
% 3.40/3.62                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.40/3.62                       ( ( m1_pre_topc @ D @ C ) =>
% 3.40/3.62                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 3.40/3.62                           ( k2_partfun1 @
% 3.40/3.62                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 3.40/3.62                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.40/3.62  thf('37', plain,
% 3.40/3.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.40/3.62         ((v2_struct_0 @ X16)
% 3.40/3.62          | ~ (v2_pre_topc @ X16)
% 3.40/3.62          | ~ (l1_pre_topc @ X16)
% 3.40/3.62          | ~ (m1_pre_topc @ X17 @ X18)
% 3.40/3.62          | ~ (m1_pre_topc @ X17 @ X19)
% 3.40/3.62          | ((k3_tmap_1 @ X18 @ X16 @ X19 @ X17 @ X20)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16) @ 
% 3.40/3.62                 X20 @ (u1_struct_0 @ X17)))
% 3.40/3.62          | ~ (m1_subset_1 @ X20 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))))
% 3.40/3.62          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))
% 3.40/3.62          | ~ (v1_funct_1 @ X20)
% 3.40/3.62          | ~ (m1_pre_topc @ X19 @ X18)
% 3.40/3.62          | ~ (l1_pre_topc @ X18)
% 3.40/3.62          | ~ (v2_pre_topc @ X18)
% 3.40/3.62          | (v2_struct_0 @ X18))),
% 3.40/3.62      inference('cnf', [status(esa)], [d5_tmap_1])).
% 3.40/3.62  thf('38', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((v2_struct_0 @ X0)
% 3.40/3.62          | ~ (v2_pre_topc @ X0)
% 3.40/3.62          | ~ (l1_pre_topc @ X0)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X0)
% 3.40/3.62          | ~ (v1_funct_1 @ sk_E)
% 3.40/3.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X1)))
% 3.40/3.62          | ~ (m1_pre_topc @ X1 @ sk_A)
% 3.40/3.62          | ~ (m1_pre_topc @ X1 @ X0)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('sup-', [status(thm)], ['36', '37'])).
% 3.40/3.62  thf('39', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('40', plain,
% 3.40/3.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('43', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((v2_struct_0 @ X0)
% 3.40/3.62          | ~ (v2_pre_topc @ X0)
% 3.40/3.62          | ~ (l1_pre_topc @ X0)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X0)
% 3.40/3.62          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X1)))
% 3.40/3.62          | ~ (m1_pre_topc @ X1 @ sk_A)
% 3.40/3.62          | ~ (m1_pre_topc @ X1 @ X0)
% 3.40/3.62          | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 3.40/3.62  thf('44', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X0)))
% 3.40/3.62          | ~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_A))),
% 3.40/3.62      inference('sup-', [status(thm)], ['35', '43'])).
% 3.40/3.62  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('48', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         ((v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X0)))
% 3.40/3.62          | (v2_struct_0 @ sk_A))),
% 3.40/3.62      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 3.40/3.62  thf('49', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         ((v2_struct_0 @ sk_A)
% 3.40/3.62          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X0)))
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('simplify', [status(thm)], ['48'])).
% 3.40/3.62  thf('50', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_D)))
% 3.40/3.62        | (v2_struct_0 @ sk_A))),
% 3.40/3.62      inference('sup-', [status(thm)], ['34', '49'])).
% 3.40/3.62  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('52', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_A)
% 3.40/3.62        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_D))))),
% 3.40/3.62      inference('clc', [status(thm)], ['50', '51'])).
% 3.40/3.62  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('54', plain,
% 3.40/3.62      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 3.40/3.62         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.62            (u1_struct_0 @ sk_D)))),
% 3.40/3.62      inference('clc', [status(thm)], ['52', '53'])).
% 3.40/3.62  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('56', plain,
% 3.40/3.62      ((m1_subset_1 @ sk_E @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf(d4_tmap_1, axiom,
% 3.40/3.62    (![A:$i]:
% 3.40/3.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.40/3.62       ( ![B:$i]:
% 3.40/3.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.40/3.62             ( l1_pre_topc @ B ) ) =>
% 3.40/3.62           ( ![C:$i]:
% 3.40/3.62             ( ( ( v1_funct_1 @ C ) & 
% 3.40/3.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62                 ( m1_subset_1 @
% 3.40/3.62                   C @ 
% 3.40/3.62                   ( k1_zfmisc_1 @
% 3.40/3.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.40/3.62               ( ![D:$i]:
% 3.40/3.62                 ( ( m1_pre_topc @ D @ A ) =>
% 3.40/3.62                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 3.40/3.62                     ( k2_partfun1 @
% 3.40/3.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 3.40/3.62                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 3.40/3.62  thf('57', plain,
% 3.40/3.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.40/3.62         ((v2_struct_0 @ X12)
% 3.40/3.62          | ~ (v2_pre_topc @ X12)
% 3.40/3.62          | ~ (l1_pre_topc @ X12)
% 3.40/3.62          | ~ (m1_pre_topc @ X13 @ X14)
% 3.40/3.62          | ((k2_tmap_1 @ X14 @ X12 @ X15 @ X13)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 3.40/3.62                 X15 @ (u1_struct_0 @ X13)))
% 3.40/3.62          | ~ (m1_subset_1 @ X15 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 3.40/3.62          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 3.40/3.62          | ~ (v1_funct_1 @ X15)
% 3.40/3.62          | ~ (l1_pre_topc @ X14)
% 3.40/3.62          | ~ (v2_pre_topc @ X14)
% 3.40/3.62          | (v2_struct_0 @ X14))),
% 3.40/3.62      inference('cnf', [status(esa)], [d4_tmap_1])).
% 3.40/3.62  thf('58', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         ((v2_struct_0 @ sk_A)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_A)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (v1_funct_1 @ sk_E)
% 3.40/3.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X0)))
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('sup-', [status(thm)], ['56', '57'])).
% 3.40/3.62  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('62', plain,
% 3.40/3.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('64', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('65', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         ((v2_struct_0 @ sk_A)
% 3.40/3.62          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X0)))
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('demod', [status(thm)],
% 3.40/3.62                ['58', '59', '60', '61', '62', '63', '64'])).
% 3.40/3.62  thf('66', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_D)))
% 3.40/3.62        | (v2_struct_0 @ sk_A))),
% 3.40/3.62      inference('sup-', [status(thm)], ['55', '65'])).
% 3.40/3.62  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('68', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_A)
% 3.40/3.62        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_D))))),
% 3.40/3.62      inference('clc', [status(thm)], ['66', '67'])).
% 3.40/3.62  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('70', plain,
% 3.40/3.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 3.40/3.62         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.62            (u1_struct_0 @ sk_D)))),
% 3.40/3.62      inference('clc', [status(thm)], ['68', '69'])).
% 3.40/3.62  thf('71', plain,
% 3.40/3.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 3.40/3.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 3.40/3.62      inference('sup+', [status(thm)], ['54', '70'])).
% 3.40/3.62  thf('72', plain,
% 3.40/3.62      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('demod', [status(thm)], ['33', '71'])).
% 3.40/3.62  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('74', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_A)
% 3.40/3.62          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62             (k1_zfmisc_1 @ 
% 3.40/3.62              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 3.40/3.62      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 3.40/3.62  thf('75', plain,
% 3.40/3.62      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 3.40/3.62         (k1_zfmisc_1 @ 
% 3.40/3.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 3.40/3.62        | (v2_struct_0 @ sk_A)
% 3.40/3.62        | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('sup-', [status(thm)], ['73', '74'])).
% 3.40/3.62  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('77', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 3.40/3.62           (k1_zfmisc_1 @ 
% 3.40/3.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 3.40/3.62      inference('clc', [status(thm)], ['75', '76'])).
% 3.40/3.62  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('79', plain,
% 3.40/3.62      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('clc', [status(thm)], ['77', '78'])).
% 3.40/3.62  thf('80', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('81', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         ((v2_struct_0 @ sk_A)
% 3.40/3.62          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X0)))
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('simplify', [status(thm)], ['48'])).
% 3.40/3.62  thf('82', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_C)))
% 3.40/3.62        | (v2_struct_0 @ sk_A))),
% 3.40/3.62      inference('sup-', [status(thm)], ['80', '81'])).
% 3.40/3.62  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('84', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_A)
% 3.40/3.62        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_C))))),
% 3.40/3.62      inference('clc', [status(thm)], ['82', '83'])).
% 3.40/3.62  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('86', plain,
% 3.40/3.62      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 3.40/3.62         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.62            (u1_struct_0 @ sk_C)))),
% 3.40/3.62      inference('clc', [status(thm)], ['84', '85'])).
% 3.40/3.62  thf('87', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('88', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         ((v2_struct_0 @ sk_A)
% 3.40/3.62          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 3.40/3.62              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62                 sk_E @ (u1_struct_0 @ X0)))
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('demod', [status(thm)],
% 3.40/3.62                ['58', '59', '60', '61', '62', '63', '64'])).
% 3.40/3.62  thf('89', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_C)))
% 3.40/3.62        | (v2_struct_0 @ sk_A))),
% 3.40/3.62      inference('sup-', [status(thm)], ['87', '88'])).
% 3.40/3.62  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('91', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_A)
% 3.40/3.62        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 3.40/3.62            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.62               sk_E @ (u1_struct_0 @ sk_C))))),
% 3.40/3.62      inference('clc', [status(thm)], ['89', '90'])).
% 3.40/3.62  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('93', plain,
% 3.40/3.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 3.40/3.62         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.62            (u1_struct_0 @ sk_C)))),
% 3.40/3.62      inference('clc', [status(thm)], ['91', '92'])).
% 3.40/3.62  thf('94', plain,
% 3.40/3.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 3.40/3.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 3.40/3.62      inference('sup+', [status(thm)], ['86', '93'])).
% 3.40/3.62  thf('95', plain,
% 3.40/3.62      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('demod', [status(thm)], ['79', '94'])).
% 3.40/3.62  thf(dt_k10_tmap_1, axiom,
% 3.40/3.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.40/3.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.40/3.62         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 3.40/3.62         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 3.40/3.62         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 3.40/3.62         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 3.40/3.62         ( v1_funct_1 @ E ) & 
% 3.40/3.62         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62         ( m1_subset_1 @
% 3.40/3.62           E @ 
% 3.40/3.62           ( k1_zfmisc_1 @
% 3.40/3.62             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 3.40/3.62         ( v1_funct_1 @ F ) & 
% 3.40/3.62         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62         ( m1_subset_1 @
% 3.40/3.62           F @ 
% 3.40/3.62           ( k1_zfmisc_1 @
% 3.40/3.62             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.40/3.62       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.40/3.62         ( v1_funct_2 @
% 3.40/3.62           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.40/3.62           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 3.40/3.62         ( m1_subset_1 @
% 3.40/3.62           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.40/3.62           ( k1_zfmisc_1 @
% 3.40/3.62             ( k2_zfmisc_1 @
% 3.40/3.62               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 3.40/3.62               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 3.40/3.62  thf('96', plain,
% 3.40/3.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.40/3.62         (~ (m1_subset_1 @ X21 @ 
% 3.40/3.62             (k1_zfmisc_1 @ 
% 3.40/3.62              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 3.40/3.62          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 3.40/3.62          | ~ (v1_funct_1 @ X21)
% 3.40/3.62          | ~ (m1_pre_topc @ X24 @ X25)
% 3.40/3.62          | (v2_struct_0 @ X24)
% 3.40/3.62          | ~ (m1_pre_topc @ X22 @ X25)
% 3.40/3.62          | (v2_struct_0 @ X22)
% 3.40/3.62          | ~ (l1_pre_topc @ X23)
% 3.40/3.62          | ~ (v2_pre_topc @ X23)
% 3.40/3.62          | (v2_struct_0 @ X23)
% 3.40/3.62          | ~ (l1_pre_topc @ X25)
% 3.40/3.62          | ~ (v2_pre_topc @ X25)
% 3.40/3.62          | (v2_struct_0 @ X25)
% 3.40/3.62          | ~ (v1_funct_1 @ X26)
% 3.40/3.62          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 3.40/3.62          | ~ (m1_subset_1 @ X26 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 3.40/3.62          | (v1_funct_1 @ (k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26)))),
% 3.40/3.62      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 3.40/3.62  thf('97', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.62         ((v1_funct_1 @ 
% 3.40/3.62           (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ 
% 3.40/3.62            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X0))
% 3.40/3.62          | ~ (m1_subset_1 @ X0 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 3.40/3.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ~ (v1_funct_1 @ X0)
% 3.40/3.62          | (v2_struct_0 @ X2)
% 3.40/3.62          | ~ (v2_pre_topc @ X2)
% 3.40/3.62          | ~ (l1_pre_topc @ X2)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_C)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_C @ X2)
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X1 @ X2)
% 3.40/3.62          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 3.40/3.62          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.62               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.62      inference('sup-', [status(thm)], ['95', '96'])).
% 3.40/3.62  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('100', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('101', plain,
% 3.40/3.62      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 3.40/3.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.40/3.62  thf('102', plain,
% 3.40/3.62      ((m1_subset_1 @ sk_E @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('103', plain,
% 3.40/3.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ X27 @ X28)
% 3.40/3.62          | ~ (m1_pre_topc @ X29 @ X28)
% 3.40/3.62          | ~ (l1_pre_topc @ X30)
% 3.40/3.62          | ~ (v2_pre_topc @ X30)
% 3.40/3.62          | (v2_struct_0 @ X30)
% 3.40/3.62          | ~ (l1_pre_topc @ X28)
% 3.40/3.62          | ~ (v2_pre_topc @ X28)
% 3.40/3.62          | (v2_struct_0 @ X28)
% 3.40/3.62          | ~ (v1_funct_1 @ X31)
% 3.40/3.62          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 3.40/3.62          | ~ (m1_subset_1 @ X31 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 3.40/3.62          | (v1_funct_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31)))),
% 3.40/3.62      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 3.40/3.62  thf('104', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 3.40/3.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ~ (v1_funct_1 @ sk_E)
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (v2_pre_topc @ X1)
% 3.40/3.62          | ~ (l1_pre_topc @ X1)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.62      inference('sup-', [status(thm)], ['102', '103'])).
% 3.40/3.62  thf('105', plain,
% 3.40/3.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('106', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('107', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('109', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (v2_pre_topc @ X1)
% 3.40/3.62          | ~ (l1_pre_topc @ X1)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.62      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 3.40/3.62  thf('110', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_A)
% 3.40/3.62          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 3.40/3.62      inference('sup-', [status(thm)], ['101', '109'])).
% 3.40/3.62  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('114', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_A)
% 3.40/3.62          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 3.40/3.62      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 3.40/3.62  thf('115', plain,
% 3.40/3.62      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 3.40/3.62        | (v2_struct_0 @ sk_A)
% 3.40/3.62        | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('sup-', [status(thm)], ['100', '114'])).
% 3.40/3.62  thf('116', plain,
% 3.40/3.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 3.40/3.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 3.40/3.62      inference('sup+', [status(thm)], ['86', '93'])).
% 3.40/3.62  thf('117', plain,
% 3.40/3.62      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 3.40/3.62        | (v2_struct_0 @ sk_A)
% 3.40/3.62        | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('demod', [status(thm)], ['115', '116'])).
% 3.40/3.62  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('119', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 3.40/3.62      inference('clc', [status(thm)], ['117', '118'])).
% 3.40/3.62  thf('120', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('121', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 3.40/3.62      inference('clc', [status(thm)], ['119', '120'])).
% 3.40/3.62  thf('122', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.62         ((v1_funct_1 @ 
% 3.40/3.62           (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ 
% 3.40/3.62            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X0))
% 3.40/3.62          | ~ (m1_subset_1 @ X0 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 3.40/3.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ~ (v1_funct_1 @ X0)
% 3.40/3.62          | (v2_struct_0 @ X2)
% 3.40/3.62          | ~ (v2_pre_topc @ X2)
% 3.40/3.62          | ~ (l1_pre_topc @ X2)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_C)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_C @ X2)
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X1 @ X2)
% 3.40/3.62          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.62               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.62      inference('demod', [status(thm)], ['97', '98', '99', '121'])).
% 3.40/3.62  thf('123', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('124', plain,
% 3.40/3.62      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 3.40/3.62      inference('cnf', [status(esa)], [t2_tsep_1])).
% 3.40/3.62  thf('125', plain,
% 3.40/3.62      ((m1_subset_1 @ sk_E @ 
% 3.40/3.62        (k1_zfmisc_1 @ 
% 3.40/3.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('126', plain,
% 3.40/3.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ X27 @ X28)
% 3.40/3.62          | ~ (m1_pre_topc @ X29 @ X28)
% 3.40/3.62          | ~ (l1_pre_topc @ X30)
% 3.40/3.62          | ~ (v2_pre_topc @ X30)
% 3.40/3.62          | (v2_struct_0 @ X30)
% 3.40/3.62          | ~ (l1_pre_topc @ X28)
% 3.40/3.62          | ~ (v2_pre_topc @ X28)
% 3.40/3.62          | (v2_struct_0 @ X28)
% 3.40/3.62          | ~ (v1_funct_1 @ X31)
% 3.40/3.62          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 3.40/3.62          | ~ (m1_subset_1 @ X31 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 3.40/3.62          | (v1_funct_2 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 3.40/3.62             (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))),
% 3.40/3.62      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 3.40/3.62  thf('127', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ~ (v1_funct_1 @ sk_E)
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (v2_pre_topc @ X1)
% 3.40/3.62          | ~ (l1_pre_topc @ X1)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.62      inference('sup-', [status(thm)], ['125', '126'])).
% 3.40/3.62  thf('128', plain,
% 3.40/3.62      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('129', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('130', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('132', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i]:
% 3.40/3.62         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (v2_pre_topc @ X1)
% 3.40/3.62          | ~ (l1_pre_topc @ X1)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_A @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.62      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 3.40/3.62  thf('133', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | ~ (l1_pre_topc @ sk_A)
% 3.40/3.62          | ~ (v2_pre_topc @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_A)
% 3.40/3.62          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.62      inference('sup-', [status(thm)], ['124', '132'])).
% 3.40/3.62  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('137', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_A)
% 3.40/3.62          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.62             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.62      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 3.40/3.62  thf('138', plain,
% 3.40/3.62      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 3.40/3.62         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.40/3.62        | (v2_struct_0 @ sk_A)
% 3.40/3.62        | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('sup-', [status(thm)], ['123', '137'])).
% 3.40/3.62  thf('139', plain,
% 3.40/3.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 3.40/3.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 3.40/3.62      inference('sup+', [status(thm)], ['86', '93'])).
% 3.40/3.62  thf('140', plain,
% 3.40/3.62      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.62         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.40/3.62        | (v2_struct_0 @ sk_A)
% 3.40/3.62        | (v2_struct_0 @ sk_B))),
% 3.40/3.62      inference('demod', [status(thm)], ['138', '139'])).
% 3.40/3.62  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('142', plain,
% 3.40/3.62      (((v2_struct_0 @ sk_B)
% 3.40/3.62        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.62           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.62      inference('clc', [status(thm)], ['140', '141'])).
% 3.40/3.62  thf('143', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.62  thf('144', plain,
% 3.40/3.62      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.62        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.40/3.62      inference('clc', [status(thm)], ['142', '143'])).
% 3.40/3.62  thf('145', plain,
% 3.40/3.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.62         ((v1_funct_1 @ 
% 3.40/3.62           (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ 
% 3.40/3.62            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X0))
% 3.40/3.62          | ~ (m1_subset_1 @ X0 @ 
% 3.40/3.62               (k1_zfmisc_1 @ 
% 3.40/3.62                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 3.40/3.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 3.40/3.62          | ~ (v1_funct_1 @ X0)
% 3.40/3.62          | (v2_struct_0 @ X2)
% 3.40/3.62          | ~ (v2_pre_topc @ X2)
% 3.40/3.62          | ~ (l1_pre_topc @ X2)
% 3.40/3.62          | (v2_struct_0 @ sk_B)
% 3.40/3.62          | (v2_struct_0 @ sk_C)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_C @ X2)
% 3.40/3.62          | (v2_struct_0 @ X1)
% 3.40/3.62          | ~ (m1_pre_topc @ X1 @ X2))),
% 3.40/3.62      inference('demod', [status(thm)], ['122', '144'])).
% 3.40/3.62  thf('146', plain,
% 3.40/3.62      (![X0 : $i]:
% 3.40/3.62         (~ (m1_pre_topc @ sk_D @ X0)
% 3.40/3.62          | (v2_struct_0 @ sk_D)
% 3.40/3.62          | ~ (m1_pre_topc @ sk_C @ X0)
% 3.40/3.62          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 3.40/3.63          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | (v1_funct_1 @ 
% 3.40/3.63             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 3.40/3.63      inference('sup-', [status(thm)], ['72', '145'])).
% 3.40/3.63  thf('147', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('148', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_A)
% 3.40/3.63          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 3.40/3.63      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 3.40/3.63  thf('149', plain,
% 3.40/3.63      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B))),
% 3.40/3.63      inference('sup-', [status(thm)], ['147', '148'])).
% 3.40/3.63  thf('150', plain,
% 3.40/3.63      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 3.40/3.63         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 3.40/3.63      inference('sup+', [status(thm)], ['54', '70'])).
% 3.40/3.63  thf('151', plain,
% 3.40/3.63      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B))),
% 3.40/3.63      inference('demod', [status(thm)], ['149', '150'])).
% 3.40/3.63  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('153', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_B)
% 3.40/3.63        | (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 3.40/3.63      inference('clc', [status(thm)], ['151', '152'])).
% 3.40/3.63  thf('154', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('155', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 3.40/3.63      inference('clc', [status(thm)], ['153', '154'])).
% 3.40/3.63  thf('156', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('157', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (m1_pre_topc @ X0 @ sk_A)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_A)
% 3.40/3.63          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 3.40/3.63             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 3.40/3.63  thf('158', plain,
% 3.40/3.63      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 3.40/3.63         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B))),
% 3.40/3.63      inference('sup-', [status(thm)], ['156', '157'])).
% 3.40/3.63  thf('159', plain,
% 3.40/3.63      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 3.40/3.63         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 3.40/3.63      inference('sup+', [status(thm)], ['54', '70'])).
% 3.40/3.63  thf('160', plain,
% 3.40/3.63      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B))),
% 3.40/3.63      inference('demod', [status(thm)], ['158', '159'])).
% 3.40/3.63  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('162', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_B)
% 3.40/3.63        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('clc', [status(thm)], ['160', '161'])).
% 3.40/3.63  thf('163', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('164', plain,
% 3.40/3.63      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 3.40/3.63      inference('clc', [status(thm)], ['162', '163'])).
% 3.40/3.63  thf('165', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (m1_pre_topc @ sk_D @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_D)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | (v1_funct_1 @ 
% 3.40/3.63             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 3.40/3.63      inference('demod', [status(thm)], ['146', '155', '164'])).
% 3.40/3.63  thf('166', plain,
% 3.40/3.63      (((v1_funct_1 @ 
% 3.40/3.63         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | ~ (v2_pre_topc @ sk_A)
% 3.40/3.63        | ~ (l1_pre_topc @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('sup-', [status(thm)], ['13', '165'])).
% 3.40/3.63  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('169', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('170', plain,
% 3.40/3.63      (((v1_funct_1 @ 
% 3.40/3.63         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 3.40/3.63  thf('171', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('172', plain,
% 3.40/3.63      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63        (k1_zfmisc_1 @ 
% 3.40/3.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.63      inference('demod', [status(thm)], ['33', '71'])).
% 3.40/3.63  thf('173', plain,
% 3.40/3.63      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63        (k1_zfmisc_1 @ 
% 3.40/3.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.63      inference('demod', [status(thm)], ['79', '94'])).
% 3.40/3.63  thf('174', plain,
% 3.40/3.63      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.40/3.63         (~ (m1_subset_1 @ X21 @ 
% 3.40/3.63             (k1_zfmisc_1 @ 
% 3.40/3.63              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 3.40/3.63          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 3.40/3.63          | ~ (v1_funct_1 @ X21)
% 3.40/3.63          | ~ (m1_pre_topc @ X24 @ X25)
% 3.40/3.63          | (v2_struct_0 @ X24)
% 3.40/3.63          | ~ (m1_pre_topc @ X22 @ X25)
% 3.40/3.63          | (v2_struct_0 @ X22)
% 3.40/3.63          | ~ (l1_pre_topc @ X23)
% 3.40/3.63          | ~ (v2_pre_topc @ X23)
% 3.40/3.63          | (v2_struct_0 @ X23)
% 3.40/3.63          | ~ (l1_pre_topc @ X25)
% 3.40/3.63          | ~ (v2_pre_topc @ X25)
% 3.40/3.63          | (v2_struct_0 @ X25)
% 3.40/3.63          | ~ (v1_funct_1 @ X26)
% 3.40/3.63          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 3.40/3.63          | ~ (m1_subset_1 @ X26 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 3.40/3.63          | (v1_funct_2 @ (k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26) @ 
% 3.40/3.63             (u1_struct_0 @ (k1_tsep_1 @ X25 @ X22 @ X24)) @ 
% 3.40/3.63             (u1_struct_0 @ X23)))),
% 3.40/3.63      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 3.40/3.63  thf('175', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.63         ((v1_funct_2 @ 
% 3.40/3.63           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 3.40/3.63           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (m1_subset_1 @ X2 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X2)
% 3.40/3.63          | (v2_struct_0 @ X1)
% 3.40/3.63          | ~ (v2_pre_topc @ X1)
% 3.40/3.63          | ~ (l1_pre_topc @ X1)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X1)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (m1_pre_topc @ X0 @ X1)
% 3.40/3.63          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 3.40/3.63          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('sup-', [status(thm)], ['173', '174'])).
% 3.40/3.63  thf('176', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('178', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.63         ((v1_funct_2 @ 
% 3.40/3.63           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 3.40/3.63           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (m1_subset_1 @ X2 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X2)
% 3.40/3.63          | (v2_struct_0 @ X1)
% 3.40/3.63          | ~ (v2_pre_topc @ X1)
% 3.40/3.63          | ~ (l1_pre_topc @ X1)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X1)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (m1_pre_topc @ X0 @ X1)
% 3.40/3.63          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 3.40/3.63          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('demod', [status(thm)], ['175', '176', '177'])).
% 3.40/3.63  thf('179', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 3.40/3.63      inference('clc', [status(thm)], ['119', '120'])).
% 3.40/3.63  thf('180', plain,
% 3.40/3.63      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.40/3.63      inference('clc', [status(thm)], ['142', '143'])).
% 3.40/3.63  thf('181', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.63         ((v1_funct_2 @ 
% 3.40/3.63           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 3.40/3.63           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (m1_subset_1 @ X2 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X2)
% 3.40/3.63          | (v2_struct_0 @ X1)
% 3.40/3.63          | ~ (v2_pre_topc @ X1)
% 3.40/3.63          | ~ (l1_pre_topc @ X1)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X1)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.63      inference('demod', [status(thm)], ['178', '179', '180'])).
% 3.40/3.63  thf('182', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (m1_pre_topc @ sk_D @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_D)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 3.40/3.63          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | (v1_funct_2 @ 
% 3.40/3.63             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('sup-', [status(thm)], ['172', '181'])).
% 3.40/3.63  thf('183', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 3.40/3.63      inference('clc', [status(thm)], ['153', '154'])).
% 3.40/3.63  thf('184', plain,
% 3.40/3.63      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 3.40/3.63      inference('clc', [status(thm)], ['162', '163'])).
% 3.40/3.63  thf('185', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (m1_pre_topc @ sk_D @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_D)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | (v1_funct_2 @ 
% 3.40/3.63             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('demod', [status(thm)], ['182', '183', '184'])).
% 3.40/3.63  thf('186', plain,
% 3.40/3.63      (((v1_funct_2 @ 
% 3.40/3.63         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 3.40/3.63         (u1_struct_0 @ sk_B))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | ~ (v2_pre_topc @ sk_A)
% 3.40/3.63        | ~ (l1_pre_topc @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('sup-', [status(thm)], ['171', '185'])).
% 3.40/3.63  thf('187', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('188', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('190', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('191', plain,
% 3.40/3.63      (((v1_funct_2 @ 
% 3.40/3.63         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 3.40/3.63  thf('192', plain,
% 3.40/3.63      ((m1_subset_1 @ sk_E @ 
% 3.40/3.63        (k1_zfmisc_1 @ 
% 3.40/3.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('193', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf(t138_tmap_1, axiom,
% 3.40/3.63    (![A:$i]:
% 3.40/3.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.40/3.63       ( ![B:$i]:
% 3.40/3.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 3.40/3.63             ( l1_pre_topc @ B ) ) =>
% 3.40/3.63           ( ![C:$i]:
% 3.40/3.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 3.40/3.63               ( ![D:$i]:
% 3.40/3.63                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 3.40/3.63                   ( ![E:$i]:
% 3.40/3.63                     ( ( ( v1_funct_1 @ E ) & 
% 3.40/3.63                         ( v1_funct_2 @
% 3.40/3.63                           E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 3.40/3.63                           ( u1_struct_0 @ B ) ) & 
% 3.40/3.63                         ( m1_subset_1 @
% 3.40/3.63                           E @ 
% 3.40/3.63                           ( k1_zfmisc_1 @
% 3.40/3.63                             ( k2_zfmisc_1 @
% 3.40/3.63                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 3.40/3.63                               ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.40/3.63                       ( r2_funct_2 @
% 3.40/3.63                         ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 3.40/3.63                         ( u1_struct_0 @ B ) @ E @ 
% 3.40/3.63                         ( k10_tmap_1 @
% 3.40/3.63                           A @ B @ C @ D @ 
% 3.40/3.63                           ( k3_tmap_1 @
% 3.40/3.63                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 3.40/3.63                           ( k3_tmap_1 @
% 3.40/3.63                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.40/3.63  thf('194', plain,
% 3.40/3.63      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.40/3.63         ((v2_struct_0 @ X32)
% 3.40/3.63          | ~ (v2_pre_topc @ X32)
% 3.40/3.63          | ~ (l1_pre_topc @ X32)
% 3.40/3.63          | (v2_struct_0 @ X33)
% 3.40/3.63          | ~ (m1_pre_topc @ X33 @ X34)
% 3.40/3.63          | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ X34 @ X35 @ X33)) @ 
% 3.40/3.63             (u1_struct_0 @ X32) @ X36 @ 
% 3.40/3.63             (k10_tmap_1 @ X34 @ X32 @ X35 @ X33 @ 
% 3.40/3.63              (k3_tmap_1 @ X34 @ X32 @ (k1_tsep_1 @ X34 @ X35 @ X33) @ X35 @ 
% 3.40/3.63               X36) @ 
% 3.40/3.63              (k3_tmap_1 @ X34 @ X32 @ (k1_tsep_1 @ X34 @ X35 @ X33) @ X33 @ 
% 3.40/3.63               X36)))
% 3.40/3.63          | ~ (m1_subset_1 @ X36 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X34 @ X35 @ X33)) @ 
% 3.40/3.63                 (u1_struct_0 @ X32))))
% 3.40/3.63          | ~ (v1_funct_2 @ X36 @ 
% 3.40/3.63               (u1_struct_0 @ (k1_tsep_1 @ X34 @ X35 @ X33)) @ 
% 3.40/3.63               (u1_struct_0 @ X32))
% 3.40/3.63          | ~ (v1_funct_1 @ X36)
% 3.40/3.63          | ~ (m1_pre_topc @ X35 @ X34)
% 3.40/3.63          | (v2_struct_0 @ X35)
% 3.40/3.63          | ~ (l1_pre_topc @ X34)
% 3.40/3.63          | ~ (v2_pre_topc @ X34)
% 3.40/3.63          | (v2_struct_0 @ X34))),
% 3.40/3.63      inference('cnf', [status(esa)], [t138_tmap_1])).
% 3.40/3.63  thf('195', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i]:
% 3.40/3.63         (~ (m1_subset_1 @ X1 @ 
% 3.40/3.63             (k1_zfmisc_1 @ 
% 3.40/3.63              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 3.40/3.63          | (v2_struct_0 @ sk_A)
% 3.40/3.63          | ~ (v2_pre_topc @ sk_A)
% 3.40/3.63          | ~ (l1_pre_topc @ sk_A)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.40/3.63          | ~ (v1_funct_1 @ X1)
% 3.40/3.63          | ~ (v1_funct_2 @ X1 @ 
% 3.40/3.63               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 3.40/3.63               (u1_struct_0 @ X0))
% 3.40/3.63          | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ X0) @ X1 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ 
% 3.40/3.63              (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.40/3.63               sk_C @ X1) @ 
% 3.40/3.63              (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.40/3.63               sk_D @ X1)))
% 3.40/3.63          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 3.40/3.63          | (v2_struct_0 @ sk_D)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0))),
% 3.40/3.63      inference('sup-', [status(thm)], ['193', '194'])).
% 3.40/3.63  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('198', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('199', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('200', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('201', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('202', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('203', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('204', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i]:
% 3.40/3.63         (~ (m1_subset_1 @ X1 @ 
% 3.40/3.63             (k1_zfmisc_1 @ 
% 3.40/3.63              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 3.40/3.63          | (v2_struct_0 @ sk_A)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (v1_funct_1 @ X1)
% 3.40/3.63          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.40/3.63          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ 
% 3.40/3.63              (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1) @ 
% 3.40/3.63              (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1)))
% 3.40/3.63          | (v2_struct_0 @ sk_D)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0))),
% 3.40/3.63      inference('demod', [status(thm)],
% 3.40/3.63                ['195', '196', '197', '198', '199', '200', '201', '202', '203'])).
% 3.40/3.63  thf('205', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_B)
% 3.40/3.63        | ~ (v2_pre_topc @ sk_B)
% 3.40/3.63        | ~ (l1_pre_topc @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_D)
% 3.40/3.63        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.63           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 3.40/3.63            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 3.40/3.63        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | ~ (v1_funct_1 @ sk_E)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_A))),
% 3.40/3.63      inference('sup-', [status(thm)], ['192', '204'])).
% 3.40/3.63  thf('206', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('207', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('208', plain,
% 3.40/3.63      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 3.40/3.63         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 3.40/3.63      inference('sup+', [status(thm)], ['86', '93'])).
% 3.40/3.63  thf('209', plain,
% 3.40/3.63      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 3.40/3.63         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 3.40/3.63      inference('sup+', [status(thm)], ['54', '70'])).
% 3.40/3.63  thf('210', plain,
% 3.40/3.63      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('211', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('212', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_D)
% 3.40/3.63        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.63           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_A))),
% 3.40/3.63      inference('demod', [status(thm)],
% 3.40/3.63                ['205', '206', '207', '208', '209', '210', '211'])).
% 3.40/3.63  thf('213', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('214', plain,
% 3.40/3.63      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63        (k1_zfmisc_1 @ 
% 3.40/3.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.63      inference('demod', [status(thm)], ['33', '71'])).
% 3.40/3.63  thf('215', plain,
% 3.40/3.63      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63        (k1_zfmisc_1 @ 
% 3.40/3.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.63      inference('demod', [status(thm)], ['79', '94'])).
% 3.40/3.63  thf('216', plain,
% 3.40/3.63      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.40/3.63         (~ (m1_subset_1 @ X21 @ 
% 3.40/3.63             (k1_zfmisc_1 @ 
% 3.40/3.63              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 3.40/3.63          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 3.40/3.63          | ~ (v1_funct_1 @ X21)
% 3.40/3.63          | ~ (m1_pre_topc @ X24 @ X25)
% 3.40/3.63          | (v2_struct_0 @ X24)
% 3.40/3.63          | ~ (m1_pre_topc @ X22 @ X25)
% 3.40/3.63          | (v2_struct_0 @ X22)
% 3.40/3.63          | ~ (l1_pre_topc @ X23)
% 3.40/3.63          | ~ (v2_pre_topc @ X23)
% 3.40/3.63          | (v2_struct_0 @ X23)
% 3.40/3.63          | ~ (l1_pre_topc @ X25)
% 3.40/3.63          | ~ (v2_pre_topc @ X25)
% 3.40/3.63          | (v2_struct_0 @ X25)
% 3.40/3.63          | ~ (v1_funct_1 @ X26)
% 3.40/3.63          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 3.40/3.63          | ~ (m1_subset_1 @ X26 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 3.40/3.63          | (m1_subset_1 @ (k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26) @ 
% 3.40/3.63             (k1_zfmisc_1 @ 
% 3.40/3.63              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X25 @ X22 @ X24)) @ 
% 3.40/3.63               (u1_struct_0 @ X23)))))),
% 3.40/3.63      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 3.40/3.63  thf('217', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.63         ((m1_subset_1 @ 
% 3.40/3.63           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 3.40/3.63           (k1_zfmisc_1 @ 
% 3.40/3.63            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (m1_subset_1 @ X2 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X2)
% 3.40/3.63          | (v2_struct_0 @ X1)
% 3.40/3.63          | ~ (v2_pre_topc @ X1)
% 3.40/3.63          | ~ (l1_pre_topc @ X1)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (v2_pre_topc @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X1)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (m1_pre_topc @ X0 @ X1)
% 3.40/3.63          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 3.40/3.63          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('sup-', [status(thm)], ['215', '216'])).
% 3.40/3.63  thf('218', plain, ((v2_pre_topc @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('219', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('220', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.63         ((m1_subset_1 @ 
% 3.40/3.63           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 3.40/3.63           (k1_zfmisc_1 @ 
% 3.40/3.63            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (m1_subset_1 @ X2 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X2)
% 3.40/3.63          | (v2_struct_0 @ X1)
% 3.40/3.63          | ~ (v2_pre_topc @ X1)
% 3.40/3.63          | ~ (l1_pre_topc @ X1)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X1)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (m1_pre_topc @ X0 @ X1)
% 3.40/3.63          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 3.40/3.63          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('demod', [status(thm)], ['217', '218', '219'])).
% 3.40/3.63  thf('221', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 3.40/3.63      inference('clc', [status(thm)], ['119', '120'])).
% 3.40/3.63  thf('222', plain,
% 3.40/3.63      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.40/3.63      inference('clc', [status(thm)], ['142', '143'])).
% 3.40/3.63  thf('223', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.40/3.63         ((m1_subset_1 @ 
% 3.40/3.63           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 3.40/3.63           (k1_zfmisc_1 @ 
% 3.40/3.63            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (m1_subset_1 @ X2 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X2)
% 3.40/3.63          | (v2_struct_0 @ X1)
% 3.40/3.63          | ~ (v2_pre_topc @ X1)
% 3.40/3.63          | ~ (l1_pre_topc @ X1)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X1)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (m1_pre_topc @ X0 @ X1))),
% 3.40/3.63      inference('demod', [status(thm)], ['220', '221', '222'])).
% 3.40/3.63  thf('224', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (m1_pre_topc @ sk_D @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_D)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 3.40/3.63          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | (m1_subset_1 @ 
% 3.40/3.63             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63             (k1_zfmisc_1 @ 
% 3.40/3.63              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 3.40/3.63               (u1_struct_0 @ sk_B)))))),
% 3.40/3.63      inference('sup-', [status(thm)], ['214', '223'])).
% 3.40/3.63  thf('225', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 3.40/3.63      inference('clc', [status(thm)], ['153', '154'])).
% 3.40/3.63  thf('226', plain,
% 3.40/3.63      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 3.40/3.63        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 3.40/3.63      inference('clc', [status(thm)], ['162', '163'])).
% 3.40/3.63  thf('227', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (m1_pre_topc @ sk_D @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_D)
% 3.40/3.63          | ~ (m1_pre_topc @ sk_C @ X0)
% 3.40/3.63          | (v2_struct_0 @ sk_C)
% 3.40/3.63          | (v2_struct_0 @ sk_B)
% 3.40/3.63          | ~ (l1_pre_topc @ X0)
% 3.40/3.63          | ~ (v2_pre_topc @ X0)
% 3.40/3.63          | (v2_struct_0 @ X0)
% 3.40/3.63          | (m1_subset_1 @ 
% 3.40/3.63             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63             (k1_zfmisc_1 @ 
% 3.40/3.63              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 3.40/3.63               (u1_struct_0 @ sk_B)))))),
% 3.40/3.63      inference('demod', [status(thm)], ['224', '225', '226'])).
% 3.40/3.63  thf('228', plain,
% 3.40/3.63      (((m1_subset_1 @ 
% 3.40/3.63         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63         (k1_zfmisc_1 @ 
% 3.40/3.63          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 3.40/3.63           (u1_struct_0 @ sk_B))))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | ~ (v2_pre_topc @ sk_A)
% 3.40/3.63        | ~ (l1_pre_topc @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('sup-', [status(thm)], ['213', '227'])).
% 3.40/3.63  thf('229', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('230', plain, ((v2_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('232', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('233', plain,
% 3.40/3.63      (((m1_subset_1 @ 
% 3.40/3.63         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63         (k1_zfmisc_1 @ 
% 3.40/3.63          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('demod', [status(thm)], ['228', '229', '230', '231', '232'])).
% 3.40/3.63  thf('234', plain,
% 3.40/3.63      ((m1_subset_1 @ sk_E @ 
% 3.40/3.63        (k1_zfmisc_1 @ 
% 3.40/3.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf(redefinition_r2_funct_2, axiom,
% 3.40/3.63    (![A:$i,B:$i,C:$i,D:$i]:
% 3.40/3.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.40/3.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.40/3.63         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.40/3.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.40/3.63       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.40/3.63  thf('235', plain,
% 3.40/3.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.40/3.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 3.40/3.63          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 3.40/3.63          | ~ (v1_funct_1 @ X0)
% 3.40/3.63          | ~ (v1_funct_1 @ X3)
% 3.40/3.63          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 3.40/3.63          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 3.40/3.63          | ((X0) = (X3))
% 3.40/3.63          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 3.40/3.63      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 3.40/3.63  thf('236', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.63             X0)
% 3.40/3.63          | ((sk_E) = (X0))
% 3.40/3.63          | ~ (m1_subset_1 @ X0 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X0)
% 3.40/3.63          | ~ (v1_funct_1 @ sk_E)
% 3.40/3.63          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 3.40/3.63      inference('sup-', [status(thm)], ['234', '235'])).
% 3.40/3.63  thf('237', plain, ((v1_funct_1 @ sk_E)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('238', plain,
% 3.40/3.63      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('239', plain,
% 3.40/3.63      (![X0 : $i]:
% 3.40/3.63         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.63             X0)
% 3.40/3.63          | ((sk_E) = (X0))
% 3.40/3.63          | ~ (m1_subset_1 @ X0 @ 
% 3.40/3.63               (k1_zfmisc_1 @ 
% 3.40/3.63                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.40/3.63          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.63          | ~ (v1_funct_1 @ X0))),
% 3.40/3.63      inference('demod', [status(thm)], ['236', '237', '238'])).
% 3.40/3.63  thf('240', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | ~ (v1_funct_1 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | ~ (v1_funct_2 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | ((sk_E)
% 3.40/3.63            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 3.40/3.63      inference('sup-', [status(thm)], ['233', '239'])).
% 3.40/3.63  thf('241', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | ((sk_E)
% 3.40/3.63            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | ~ (v1_funct_2 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | ~ (v1_funct_1 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('sup-', [status(thm)], ['212', '240'])).
% 3.40/3.63  thf('242', plain,
% 3.40/3.63      ((~ (v1_funct_1 @ 
% 3.40/3.63           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | ~ (v1_funct_2 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 3.40/3.63             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | ((sk_E)
% 3.40/3.63            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_A))),
% 3.40/3.63      inference('simplify', [status(thm)], ['241'])).
% 3.40/3.63  thf('243', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | ((sk_E)
% 3.40/3.63            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | ~ (v1_funct_1 @ 
% 3.40/3.63             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 3.40/3.63      inference('sup-', [status(thm)], ['191', '242'])).
% 3.40/3.63  thf('244', plain,
% 3.40/3.63      ((~ (v1_funct_1 @ 
% 3.40/3.63           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | ((sk_E)
% 3.40/3.63            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('simplify', [status(thm)], ['243'])).
% 3.40/3.63  thf('245', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | ((sk_E)
% 3.40/3.63            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 3.40/3.63      inference('sup-', [status(thm)], ['170', '244'])).
% 3.40/3.63  thf('246', plain,
% 3.40/3.63      ((((sk_E)
% 3.40/3.63          = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('simplify', [status(thm)], ['245'])).
% 3.40/3.63  thf('247', plain,
% 3.40/3.63      (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.63          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 3.40/3.63          (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.63          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('248', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('249', plain,
% 3.40/3.63      (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.63          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 3.40/3.63          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 3.40/3.63           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 3.40/3.63           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 3.40/3.63      inference('demod', [status(thm)], ['247', '248'])).
% 3.40/3.63  thf('250', plain,
% 3.40/3.63      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 3.40/3.63           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 3.40/3.63        | (v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_A))),
% 3.40/3.63      inference('sup-', [status(thm)], ['246', '249'])).
% 3.40/3.63  thf('251', plain,
% 3.40/3.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('sup-', [status(thm)], ['12', '250'])).
% 3.40/3.63  thf(fc2_struct_0, axiom,
% 3.40/3.63    (![A:$i]:
% 3.40/3.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.40/3.63       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.40/3.63  thf('252', plain,
% 3.40/3.63      (![X5 : $i]:
% 3.40/3.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 3.40/3.63          | ~ (l1_struct_0 @ X5)
% 3.40/3.63          | (v2_struct_0 @ X5))),
% 3.40/3.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 3.40/3.63  thf('253', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | ~ (l1_struct_0 @ sk_B))),
% 3.40/3.63      inference('sup-', [status(thm)], ['251', '252'])).
% 3.40/3.63  thf('254', plain, ((l1_pre_topc @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf(dt_l1_pre_topc, axiom,
% 3.40/3.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.40/3.63  thf('255', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 3.40/3.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.40/3.63  thf('256', plain, ((l1_struct_0 @ sk_B)),
% 3.40/3.63      inference('sup-', [status(thm)], ['254', '255'])).
% 3.40/3.63  thf('257', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_D)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B))),
% 3.40/3.63      inference('demod', [status(thm)], ['253', '256'])).
% 3.40/3.63  thf('258', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_A)
% 3.40/3.63        | (v2_struct_0 @ sk_B)
% 3.40/3.63        | (v2_struct_0 @ sk_C)
% 3.40/3.63        | (v2_struct_0 @ sk_D))),
% 3.40/3.63      inference('simplify', [status(thm)], ['257'])).
% 3.40/3.63  thf('259', plain, (~ (v2_struct_0 @ sk_B)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('260', plain,
% 3.40/3.63      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 3.40/3.63      inference('sup-', [status(thm)], ['258', '259'])).
% 3.40/3.63  thf('261', plain, (~ (v2_struct_0 @ sk_D)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('262', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 3.40/3.63      inference('clc', [status(thm)], ['260', '261'])).
% 3.40/3.63  thf('263', plain, (~ (v2_struct_0 @ sk_A)),
% 3.40/3.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.40/3.63  thf('264', plain, ((v2_struct_0 @ sk_C)),
% 3.40/3.63      inference('clc', [status(thm)], ['262', '263'])).
% 3.40/3.63  thf('265', plain, ($false), inference('demod', [status(thm)], ['0', '264'])).
% 3.40/3.63  
% 3.40/3.63  % SZS output end Refutation
% 3.40/3.63  
% 3.40/3.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
