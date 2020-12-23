%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oX1BLZ5zwJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:11 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  302 (2708 expanded)
%              Number of leaves         :   35 ( 795 expanded)
%              Depth                    :   35
%              Number of atoms          : 4758 (116168 expanded)
%              Number of equality atoms :   56 (1715 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

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

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( r1_funct_2 @ X7 @ X8 @ X11 @ X9 @ X6 @ X10 )
      | ( X6 != X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r1_funct_2 @ X7 @ X8 @ X11 @ X9 @ X10 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X9 )
      | ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('121',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

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

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['54','70'])).

thf('155',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['153','154'])).

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
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('179',plain,(
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
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

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
    inference(demod,[status(thm)],['179','180'])).

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
    inference(demod,[status(thm)],['153','154'])).

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
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('221',plain,(
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
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

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
    inference(demod,[status(thm)],['221','222'])).

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
    inference(demod,[status(thm)],['153','154'])).

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
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oX1BLZ5zwJ
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:00:29 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.32  % Running in FO mode
% 1.29/1.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.29/1.47  % Solved by: fo/fo7.sh
% 1.29/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.47  % done 914 iterations in 1.039s
% 1.29/1.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.29/1.47  % SZS output start Refutation
% 1.29/1.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.29/1.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.29/1.47  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.29/1.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.29/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.47  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 1.29/1.47  thf(sk_C_type, type, sk_C: $i).
% 1.29/1.47  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.29/1.47  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.29/1.47  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.29/1.47  thf(sk_E_type, type, sk_E: $i).
% 1.29/1.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.29/1.47  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.29/1.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.29/1.47  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.29/1.47  thf(sk_D_type, type, sk_D: $i).
% 1.29/1.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.29/1.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.29/1.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.47  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.29/1.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.29/1.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.29/1.47  thf(t139_tmap_1, conjecture,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.29/1.47             ( l1_pre_topc @ B ) ) =>
% 1.29/1.47           ( ![C:$i]:
% 1.29/1.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.29/1.47               ( ![D:$i]:
% 1.29/1.47                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.29/1.47                   ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 1.29/1.47                     ( ![E:$i]:
% 1.29/1.47                       ( ( ( v1_funct_1 @ E ) & 
% 1.29/1.47                           ( v1_funct_2 @
% 1.29/1.47                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47                           ( m1_subset_1 @
% 1.29/1.47                             E @ 
% 1.29/1.47                             ( k1_zfmisc_1 @
% 1.29/1.47                               ( k2_zfmisc_1 @
% 1.29/1.47                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.47                         ( r1_funct_2 @
% 1.29/1.47                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.29/1.47                           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.29/1.47                           ( u1_struct_0 @ B ) @ E @ 
% 1.29/1.47                           ( k10_tmap_1 @
% 1.29/1.47                             A @ B @ C @ D @ ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 1.29/1.47                             ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.47    (~( ![A:$i]:
% 1.29/1.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.29/1.47            ( l1_pre_topc @ A ) ) =>
% 1.29/1.47          ( ![B:$i]:
% 1.29/1.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.29/1.47                ( l1_pre_topc @ B ) ) =>
% 1.29/1.47              ( ![C:$i]:
% 1.29/1.47                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.29/1.47                  ( ![D:$i]:
% 1.29/1.47                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.29/1.47                      ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 1.29/1.47                        ( ![E:$i]:
% 1.29/1.47                          ( ( ( v1_funct_1 @ E ) & 
% 1.29/1.47                              ( v1_funct_2 @
% 1.29/1.47                                E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47                              ( m1_subset_1 @
% 1.29/1.47                                E @ 
% 1.29/1.47                                ( k1_zfmisc_1 @
% 1.29/1.47                                  ( k2_zfmisc_1 @
% 1.29/1.47                                    ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.47                            ( r1_funct_2 @
% 1.29/1.47                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.29/1.47                              ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.29/1.47                              ( u1_struct_0 @ B ) @ E @ 
% 1.29/1.47                              ( k10_tmap_1 @
% 1.29/1.47                                A @ B @ C @ D @ 
% 1.29/1.47                                ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 1.29/1.47                                ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.29/1.47    inference('cnf.neg', [status(esa)], [t139_tmap_1])).
% 1.29/1.47  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('1', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_E @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('2', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_E @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(redefinition_r1_funct_2, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.29/1.47     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.29/1.47         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.29/1.47         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.29/1.47         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.29/1.47         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.29/1.47       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.29/1.47  thf('3', plain,
% 1.29/1.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 1.29/1.47          | ~ (v1_funct_2 @ X6 @ X7 @ X8)
% 1.29/1.47          | ~ (v1_funct_1 @ X6)
% 1.29/1.47          | (v1_xboole_0 @ X9)
% 1.29/1.47          | (v1_xboole_0 @ X8)
% 1.29/1.47          | ~ (v1_funct_1 @ X10)
% 1.29/1.47          | ~ (v1_funct_2 @ X10 @ X11 @ X9)
% 1.29/1.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 1.29/1.47          | (r1_funct_2 @ X7 @ X8 @ X11 @ X9 @ X6 @ X10)
% 1.29/1.47          | ((X6) != (X10)))),
% 1.29/1.47      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.29/1.47  thf('4', plain,
% 1.29/1.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.29/1.47         ((r1_funct_2 @ X7 @ X8 @ X11 @ X9 @ X10 @ X10)
% 1.29/1.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 1.29/1.47          | ~ (v1_funct_2 @ X10 @ X11 @ X9)
% 1.29/1.47          | (v1_xboole_0 @ X8)
% 1.29/1.47          | (v1_xboole_0 @ X9)
% 1.29/1.47          | ~ (v1_funct_1 @ X10)
% 1.29/1.47          | ~ (v1_funct_2 @ X10 @ X7 @ X8)
% 1.29/1.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.29/1.47      inference('simplify', [status(thm)], ['3'])).
% 1.29/1.47  thf('5', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_E @ X1 @ X0)
% 1.29/1.47          | ~ (v1_funct_1 @ sk_E)
% 1.29/1.47          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | (v1_xboole_0 @ X0)
% 1.29/1.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (u1_struct_0 @ sk_B) @ sk_E @ sk_E))),
% 1.29/1.47      inference('sup-', [status(thm)], ['2', '4'])).
% 1.29/1.47  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('7', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('8', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_E @ X1 @ X0)
% 1.29/1.47          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | (v1_xboole_0 @ X0)
% 1.29/1.47          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (u1_struct_0 @ sk_B) @ sk_E @ sk_E))),
% 1.29/1.47      inference('demod', [status(thm)], ['5', '6', '7'])).
% 1.29/1.47  thf('9', plain,
% 1.29/1.47      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 1.29/1.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['1', '8'])).
% 1.29/1.47  thf('10', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('11', plain,
% 1.29/1.47      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 1.29/1.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('demod', [status(thm)], ['9', '10'])).
% 1.29/1.47  thf('12', plain,
% 1.29/1.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.47        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E))),
% 1.29/1.47      inference('simplify', [status(thm)], ['11'])).
% 1.29/1.47  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(t2_tsep_1, axiom,
% 1.29/1.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.29/1.47  thf('15', plain,
% 1.29/1.47      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 1.29/1.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.47  thf('16', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_E @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(dt_k3_tmap_1, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.29/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.29/1.47         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.29/1.47         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.29/1.47         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.29/1.47         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47         ( m1_subset_1 @
% 1.29/1.47           E @ 
% 1.29/1.47           ( k1_zfmisc_1 @
% 1.29/1.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.47       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.29/1.47         ( v1_funct_2 @
% 1.29/1.47           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.29/1.47           ( u1_struct_0 @ B ) ) & 
% 1.29/1.47         ( m1_subset_1 @
% 1.29/1.47           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.29/1.47           ( k1_zfmisc_1 @
% 1.29/1.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.29/1.47  thf('17', plain,
% 1.29/1.47      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X27 @ X28)
% 1.29/1.47          | ~ (m1_pre_topc @ X29 @ X28)
% 1.29/1.47          | ~ (l1_pre_topc @ X30)
% 1.29/1.47          | ~ (v2_pre_topc @ X30)
% 1.29/1.47          | (v2_struct_0 @ X30)
% 1.29/1.47          | ~ (l1_pre_topc @ X28)
% 1.29/1.47          | ~ (v2_pre_topc @ X28)
% 1.29/1.47          | (v2_struct_0 @ X28)
% 1.29/1.47          | ~ (v1_funct_1 @ X31)
% 1.29/1.47          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.29/1.47          | ~ (m1_subset_1 @ X31 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.29/1.47          | (m1_subset_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))))),
% 1.29/1.47      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.29/1.47  thf('18', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.47           (k1_zfmisc_1 @ 
% 1.29/1.47            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ~ (v1_funct_1 @ sk_E)
% 1.29/1.47          | (v2_struct_0 @ X1)
% 1.29/1.47          | ~ (v2_pre_topc @ X1)
% 1.29/1.47          | ~ (l1_pre_topc @ X1)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.47      inference('sup-', [status(thm)], ['16', '17'])).
% 1.29/1.47  thf('19', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('20', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('21', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('23', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.47           (k1_zfmisc_1 @ 
% 1.29/1.47            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47          | (v2_struct_0 @ X1)
% 1.29/1.47          | ~ (v2_pre_topc @ X1)
% 1.29/1.47          | ~ (l1_pre_topc @ X1)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.47      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 1.29/1.47  thf('24', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['15', '23'])).
% 1.29/1.47  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('28', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.29/1.47      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 1.29/1.47  thf('29', plain,
% 1.29/1.47      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.29/1.47         (k1_zfmisc_1 @ 
% 1.29/1.47          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['14', '28'])).
% 1.29/1.47  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('31', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.29/1.47           (k1_zfmisc_1 @ 
% 1.29/1.47            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 1.29/1.47      inference('clc', [status(thm)], ['29', '30'])).
% 1.29/1.47  thf('32', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('33', plain,
% 1.29/1.47      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('clc', [status(thm)], ['31', '32'])).
% 1.29/1.47  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('35', plain,
% 1.29/1.47      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 1.29/1.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.47  thf('36', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_E @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(d5_tmap_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.29/1.47             ( l1_pre_topc @ B ) ) =>
% 1.29/1.47           ( ![C:$i]:
% 1.29/1.47             ( ( m1_pre_topc @ C @ A ) =>
% 1.29/1.47               ( ![D:$i]:
% 1.29/1.47                 ( ( m1_pre_topc @ D @ A ) =>
% 1.29/1.47                   ( ![E:$i]:
% 1.29/1.47                     ( ( ( v1_funct_1 @ E ) & 
% 1.29/1.47                         ( v1_funct_2 @
% 1.29/1.47                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47                         ( m1_subset_1 @
% 1.29/1.47                           E @ 
% 1.29/1.47                           ( k1_zfmisc_1 @
% 1.29/1.47                             ( k2_zfmisc_1 @
% 1.29/1.47                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.47                       ( ( m1_pre_topc @ D @ C ) =>
% 1.29/1.47                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.29/1.47                           ( k2_partfun1 @
% 1.29/1.47                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.29/1.47                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.47  thf('37', plain,
% 1.29/1.47      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.29/1.47         ((v2_struct_0 @ X16)
% 1.29/1.47          | ~ (v2_pre_topc @ X16)
% 1.29/1.47          | ~ (l1_pre_topc @ X16)
% 1.29/1.47          | ~ (m1_pre_topc @ X17 @ X18)
% 1.29/1.47          | ~ (m1_pre_topc @ X17 @ X19)
% 1.29/1.47          | ((k3_tmap_1 @ X18 @ X16 @ X19 @ X17 @ X20)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16) @ 
% 1.29/1.47                 X20 @ (u1_struct_0 @ X17)))
% 1.29/1.47          | ~ (m1_subset_1 @ X20 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))))
% 1.29/1.47          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16))
% 1.29/1.47          | ~ (v1_funct_1 @ X20)
% 1.29/1.47          | ~ (m1_pre_topc @ X19 @ X18)
% 1.29/1.47          | ~ (l1_pre_topc @ X18)
% 1.29/1.47          | ~ (v2_pre_topc @ X18)
% 1.29/1.47          | (v2_struct_0 @ X18))),
% 1.29/1.47      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.29/1.47  thf('38', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_A @ X0)
% 1.29/1.47          | ~ (v1_funct_1 @ sk_E)
% 1.29/1.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X1)))
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['36', '37'])).
% 1.29/1.47  thf('39', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('40', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('43', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((v2_struct_0 @ X0)
% 1.29/1.47          | ~ (v2_pre_topc @ X0)
% 1.29/1.47          | ~ (l1_pre_topc @ X0)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_A @ X0)
% 1.29/1.47          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X1)))
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ X0)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 1.29/1.47  thf('44', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X0)))
% 1.29/1.47          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['35', '43'])).
% 1.29/1.47  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('48', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X0)))
% 1.29/1.47          | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.29/1.47  thf('49', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ sk_A)
% 1.29/1.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X0)))
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('simplify', [status(thm)], ['48'])).
% 1.29/1.47  thf('50', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_D)))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['34', '49'])).
% 1.29/1.47  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('52', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_D))))),
% 1.29/1.47      inference('clc', [status(thm)], ['50', '51'])).
% 1.29/1.47  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('54', plain,
% 1.29/1.47      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 1.29/1.47         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.47            (u1_struct_0 @ sk_D)))),
% 1.29/1.47      inference('clc', [status(thm)], ['52', '53'])).
% 1.29/1.47  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('56', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_E @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(d4_tmap_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.29/1.47             ( l1_pre_topc @ B ) ) =>
% 1.29/1.47           ( ![C:$i]:
% 1.29/1.47             ( ( ( v1_funct_1 @ C ) & 
% 1.29/1.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47                 ( m1_subset_1 @
% 1.29/1.47                   C @ 
% 1.29/1.47                   ( k1_zfmisc_1 @
% 1.29/1.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.47               ( ![D:$i]:
% 1.29/1.47                 ( ( m1_pre_topc @ D @ A ) =>
% 1.29/1.47                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.29/1.47                     ( k2_partfun1 @
% 1.29/1.47                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.29/1.47                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.47  thf('57', plain,
% 1.29/1.47      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.29/1.47         ((v2_struct_0 @ X12)
% 1.29/1.47          | ~ (v2_pre_topc @ X12)
% 1.29/1.47          | ~ (l1_pre_topc @ X12)
% 1.29/1.47          | ~ (m1_pre_topc @ X13 @ X14)
% 1.29/1.47          | ((k2_tmap_1 @ X14 @ X12 @ X15 @ X13)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ 
% 1.29/1.47                 X15 @ (u1_struct_0 @ X13)))
% 1.29/1.47          | ~ (m1_subset_1 @ X15 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 1.29/1.47          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 1.29/1.47          | ~ (v1_funct_1 @ X15)
% 1.29/1.47          | ~ (l1_pre_topc @ X14)
% 1.29/1.47          | ~ (v2_pre_topc @ X14)
% 1.29/1.47          | (v2_struct_0 @ X14))),
% 1.29/1.47      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.29/1.47  thf('58', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ sk_A)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (v1_funct_1 @ sk_E)
% 1.29/1.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X0)))
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['56', '57'])).
% 1.29/1.47  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('62', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('64', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('65', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ sk_A)
% 1.29/1.47          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X0)))
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('demod', [status(thm)],
% 1.29/1.47                ['58', '59', '60', '61', '62', '63', '64'])).
% 1.29/1.47  thf('66', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_D)))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['55', '65'])).
% 1.29/1.47  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('68', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_D))))),
% 1.29/1.47      inference('clc', [status(thm)], ['66', '67'])).
% 1.29/1.47  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('70', plain,
% 1.29/1.47      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.29/1.47         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.47            (u1_struct_0 @ sk_D)))),
% 1.29/1.47      inference('clc', [status(thm)], ['68', '69'])).
% 1.29/1.47  thf('71', plain,
% 1.29/1.47      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.29/1.47         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.29/1.47      inference('sup+', [status(thm)], ['54', '70'])).
% 1.29/1.47  thf('72', plain,
% 1.29/1.47      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('demod', [status(thm)], ['33', '71'])).
% 1.29/1.47  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('74', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.29/1.47      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 1.29/1.47  thf('75', plain,
% 1.29/1.47      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.29/1.47         (k1_zfmisc_1 @ 
% 1.29/1.47          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['73', '74'])).
% 1.29/1.47  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('77', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.29/1.47           (k1_zfmisc_1 @ 
% 1.29/1.47            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 1.29/1.47      inference('clc', [status(thm)], ['75', '76'])).
% 1.29/1.47  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('79', plain,
% 1.29/1.47      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('clc', [status(thm)], ['77', '78'])).
% 1.29/1.47  thf('80', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('81', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ sk_A)
% 1.29/1.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X0)))
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('simplify', [status(thm)], ['48'])).
% 1.29/1.47  thf('82', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_C)))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['80', '81'])).
% 1.29/1.47  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('84', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_C))))),
% 1.29/1.47      inference('clc', [status(thm)], ['82', '83'])).
% 1.29/1.47  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('86', plain,
% 1.29/1.47      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 1.29/1.47         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.47            (u1_struct_0 @ sk_C)))),
% 1.29/1.47      inference('clc', [status(thm)], ['84', '85'])).
% 1.29/1.47  thf('87', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('88', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((v2_struct_0 @ sk_A)
% 1.29/1.47          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 1.29/1.47              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47                 sk_E @ (u1_struct_0 @ X0)))
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('demod', [status(thm)],
% 1.29/1.47                ['58', '59', '60', '61', '62', '63', '64'])).
% 1.29/1.47  thf('89', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_C)))
% 1.29/1.47        | (v2_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['87', '88'])).
% 1.29/1.47  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('91', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_A)
% 1.29/1.47        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.29/1.47            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.47               sk_E @ (u1_struct_0 @ sk_C))))),
% 1.29/1.47      inference('clc', [status(thm)], ['89', '90'])).
% 1.29/1.47  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('93', plain,
% 1.29/1.47      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.29/1.47         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.47            (u1_struct_0 @ sk_C)))),
% 1.29/1.47      inference('clc', [status(thm)], ['91', '92'])).
% 1.29/1.47  thf('94', plain,
% 1.29/1.47      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.29/1.47         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.29/1.47      inference('sup+', [status(thm)], ['86', '93'])).
% 1.29/1.47  thf('95', plain,
% 1.29/1.47      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('demod', [status(thm)], ['79', '94'])).
% 1.29/1.47  thf(dt_k10_tmap_1, axiom,
% 1.29/1.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.29/1.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.29/1.47         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.29/1.47         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 1.29/1.47         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 1.29/1.47         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 1.29/1.47         ( v1_funct_1 @ E ) & 
% 1.29/1.47         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47         ( m1_subset_1 @
% 1.29/1.47           E @ 
% 1.29/1.47           ( k1_zfmisc_1 @
% 1.29/1.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.29/1.47         ( v1_funct_1 @ F ) & 
% 1.29/1.47         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47         ( m1_subset_1 @
% 1.29/1.47           F @ 
% 1.29/1.47           ( k1_zfmisc_1 @
% 1.29/1.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.47       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.29/1.47         ( v1_funct_2 @
% 1.29/1.47           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.29/1.47           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 1.29/1.47         ( m1_subset_1 @
% 1.29/1.47           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.29/1.47           ( k1_zfmisc_1 @
% 1.29/1.47             ( k2_zfmisc_1 @
% 1.29/1.47               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.29/1.47               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.29/1.47  thf('96', plain,
% 1.29/1.47      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X21 @ 
% 1.29/1.47             (k1_zfmisc_1 @ 
% 1.29/1.47              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 1.29/1.47          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 1.29/1.47          | ~ (v1_funct_1 @ X21)
% 1.29/1.47          | ~ (m1_pre_topc @ X24 @ X25)
% 1.29/1.47          | (v2_struct_0 @ X24)
% 1.29/1.47          | ~ (m1_pre_topc @ X22 @ X25)
% 1.29/1.47          | (v2_struct_0 @ X22)
% 1.29/1.47          | ~ (l1_pre_topc @ X23)
% 1.29/1.47          | ~ (v2_pre_topc @ X23)
% 1.29/1.47          | (v2_struct_0 @ X23)
% 1.29/1.47          | ~ (l1_pre_topc @ X25)
% 1.29/1.47          | ~ (v2_pre_topc @ X25)
% 1.29/1.47          | (v2_struct_0 @ X25)
% 1.29/1.47          | ~ (v1_funct_1 @ X26)
% 1.29/1.47          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 1.29/1.47          | ~ (m1_subset_1 @ X26 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 1.29/1.47          | (v1_funct_1 @ (k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26)))),
% 1.29/1.47      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 1.29/1.47  thf('97', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         ((v1_funct_1 @ 
% 1.29/1.47           (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ 
% 1.29/1.47            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X0))
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ~ (v1_funct_1 @ X0)
% 1.29/1.47          | (v2_struct_0 @ X2)
% 1.29/1.47          | ~ (v2_pre_topc @ X2)
% 1.29/1.47          | ~ (l1_pre_topc @ X2)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_C)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_C @ X2)
% 1.29/1.47          | (v2_struct_0 @ X1)
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.47          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 1.29/1.47          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.47               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['95', '96'])).
% 1.29/1.47  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('100', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('101', plain,
% 1.29/1.47      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 1.29/1.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.47  thf('102', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_E @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('103', plain,
% 1.29/1.47      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X27 @ X28)
% 1.29/1.47          | ~ (m1_pre_topc @ X29 @ X28)
% 1.29/1.47          | ~ (l1_pre_topc @ X30)
% 1.29/1.47          | ~ (v2_pre_topc @ X30)
% 1.29/1.47          | (v2_struct_0 @ X30)
% 1.29/1.47          | ~ (l1_pre_topc @ X28)
% 1.29/1.47          | ~ (v2_pre_topc @ X28)
% 1.29/1.47          | (v2_struct_0 @ X28)
% 1.29/1.47          | ~ (v1_funct_1 @ X31)
% 1.29/1.47          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.29/1.47          | ~ (m1_subset_1 @ X31 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.29/1.47          | (v1_funct_1 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31)))),
% 1.29/1.47      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.29/1.47  thf('104', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 1.29/1.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ~ (v1_funct_1 @ sk_E)
% 1.29/1.47          | (v2_struct_0 @ X1)
% 1.29/1.47          | ~ (v2_pre_topc @ X1)
% 1.29/1.47          | ~ (l1_pre_topc @ X1)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.47      inference('sup-', [status(thm)], ['102', '103'])).
% 1.29/1.47  thf('105', plain,
% 1.29/1.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('106', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('107', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('109', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i]:
% 1.29/1.47         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 1.29/1.47          | (v2_struct_0 @ X1)
% 1.29/1.47          | ~ (v2_pre_topc @ X1)
% 1.29/1.47          | ~ (l1_pre_topc @ X1)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.47      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 1.29/1.47  thf('110', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['101', '109'])).
% 1.29/1.47  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('114', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_A)
% 1.29/1.47          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 1.29/1.47      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 1.29/1.47  thf('115', plain,
% 1.29/1.47      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 1.29/1.47        | (v2_struct_0 @ sk_A)
% 1.29/1.47        | (v2_struct_0 @ sk_B))),
% 1.29/1.47      inference('sup-', [status(thm)], ['100', '114'])).
% 1.29/1.47  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('117', plain,
% 1.29/1.47      (((v2_struct_0 @ sk_B)
% 1.29/1.47        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 1.29/1.47      inference('clc', [status(thm)], ['115', '116'])).
% 1.29/1.47  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('119', plain,
% 1.29/1.47      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.29/1.47      inference('clc', [status(thm)], ['117', '118'])).
% 1.29/1.47  thf('120', plain,
% 1.29/1.47      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.29/1.47         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.29/1.47      inference('sup+', [status(thm)], ['86', '93'])).
% 1.29/1.47  thf('121', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 1.29/1.47      inference('demod', [status(thm)], ['119', '120'])).
% 1.29/1.47  thf('122', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         ((v1_funct_1 @ 
% 1.29/1.47           (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ 
% 1.29/1.47            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X0))
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.47               (k1_zfmisc_1 @ 
% 1.29/1.47                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 1.29/1.47          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 1.29/1.47          | ~ (v1_funct_1 @ X0)
% 1.29/1.47          | (v2_struct_0 @ X2)
% 1.29/1.47          | ~ (v2_pre_topc @ X2)
% 1.29/1.47          | ~ (l1_pre_topc @ X2)
% 1.29/1.47          | (v2_struct_0 @ sk_B)
% 1.29/1.47          | (v2_struct_0 @ sk_C)
% 1.29/1.47          | ~ (m1_pre_topc @ sk_C @ X2)
% 1.29/1.47          | (v2_struct_0 @ X1)
% 1.29/1.47          | ~ (m1_pre_topc @ X1 @ X2)
% 1.29/1.47          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.47               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.47      inference('demod', [status(thm)], ['97', '98', '99', '121'])).
% 1.29/1.47  thf('123', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('124', plain,
% 1.29/1.47      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 1.29/1.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.29/1.47  thf('125', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_E @ 
% 1.29/1.47        (k1_zfmisc_1 @ 
% 1.29/1.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('126', plain,
% 1.29/1.48      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ X27 @ X28)
% 1.29/1.48          | ~ (m1_pre_topc @ X29 @ X28)
% 1.29/1.48          | ~ (l1_pre_topc @ X30)
% 1.29/1.48          | ~ (v2_pre_topc @ X30)
% 1.29/1.48          | (v2_struct_0 @ X30)
% 1.29/1.48          | ~ (l1_pre_topc @ X28)
% 1.29/1.48          | ~ (v2_pre_topc @ X28)
% 1.29/1.48          | (v2_struct_0 @ X28)
% 1.29/1.48          | ~ (v1_funct_1 @ X31)
% 1.29/1.48          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.29/1.48          | ~ (m1_subset_1 @ X31 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.29/1.48          | (v1_funct_2 @ (k3_tmap_1 @ X28 @ X30 @ X29 @ X27 @ X31) @ 
% 1.29/1.48             (u1_struct_0 @ X27) @ (u1_struct_0 @ X30)))),
% 1.29/1.48      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.29/1.48  thf('127', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i]:
% 1.29/1.48         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.48           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ sk_E)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.48      inference('sup-', [status(thm)], ['125', '126'])).
% 1.29/1.48  thf('128', plain,
% 1.29/1.48      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('129', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('130', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('132', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i]:
% 1.29/1.48         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.48           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_A @ X1)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.48      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 1.29/1.48  thf('133', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (l1_pre_topc @ sk_A)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.48          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_A)
% 1.29/1.48          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.48             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('sup-', [status(thm)], ['124', '132'])).
% 1.29/1.48  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('137', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_A)
% 1.29/1.48          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.48             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 1.29/1.48  thf('138', plain,
% 1.29/1.48      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.29/1.48         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['123', '137'])).
% 1.29/1.48  thf('139', plain,
% 1.29/1.48      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.29/1.48         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.29/1.48      inference('sup+', [status(thm)], ['86', '93'])).
% 1.29/1.48  thf('140', plain,
% 1.29/1.48      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B))),
% 1.29/1.48      inference('demod', [status(thm)], ['138', '139'])).
% 1.29/1.48  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('142', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_B)
% 1.29/1.48        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('clc', [status(thm)], ['140', '141'])).
% 1.29/1.48  thf('143', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('144', plain,
% 1.29/1.48      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['142', '143'])).
% 1.29/1.48  thf('145', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((v1_funct_1 @ 
% 1.29/1.48           (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X0))
% 1.29/1.48          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X0)
% 1.29/1.48          | (v2_struct_0 @ X2)
% 1.29/1.48          | ~ (v2_pre_topc @ X2)
% 1.29/1.48          | ~ (l1_pre_topc @ X2)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X2)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (m1_pre_topc @ X1 @ X2))),
% 1.29/1.48      inference('demod', [status(thm)], ['122', '144'])).
% 1.29/1.48  thf('146', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ sk_D @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 1.29/1.48          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | (v1_funct_1 @ 
% 1.29/1.48             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.29/1.48      inference('sup-', [status(thm)], ['72', '145'])).
% 1.29/1.48  thf('147', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('148', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_A)
% 1.29/1.48          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 1.29/1.48      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 1.29/1.48  thf('149', plain,
% 1.29/1.48      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['147', '148'])).
% 1.29/1.48  thf('150', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('151', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_B)
% 1.29/1.48        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 1.29/1.48      inference('clc', [status(thm)], ['149', '150'])).
% 1.29/1.48  thf('152', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('153', plain,
% 1.29/1.48      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.29/1.48      inference('clc', [status(thm)], ['151', '152'])).
% 1.29/1.48  thf('154', plain,
% 1.29/1.48      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.29/1.48         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.29/1.48      inference('sup+', [status(thm)], ['54', '70'])).
% 1.29/1.48  thf('155', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 1.29/1.48      inference('demod', [status(thm)], ['153', '154'])).
% 1.29/1.48  thf('156', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('157', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_A)
% 1.29/1.48          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 1.29/1.48             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 1.29/1.48  thf('158', plain,
% 1.29/1.48      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 1.29/1.48         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['156', '157'])).
% 1.29/1.48  thf('159', plain,
% 1.29/1.48      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.29/1.48         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.29/1.48      inference('sup+', [status(thm)], ['54', '70'])).
% 1.29/1.48  thf('160', plain,
% 1.29/1.48      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B))),
% 1.29/1.48      inference('demod', [status(thm)], ['158', '159'])).
% 1.29/1.48  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('162', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_B)
% 1.29/1.48        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('clc', [status(thm)], ['160', '161'])).
% 1.29/1.48  thf('163', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('164', plain,
% 1.29/1.48      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['162', '163'])).
% 1.29/1.48  thf('165', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ sk_D @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | (v1_funct_1 @ 
% 1.29/1.48             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.29/1.48      inference('demod', [status(thm)], ['146', '155', '164'])).
% 1.29/1.48  thf('166', plain,
% 1.29/1.48      (((v1_funct_1 @ 
% 1.29/1.48         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.48        | ~ (l1_pre_topc @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('sup-', [status(thm)], ['13', '165'])).
% 1.29/1.48  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('169', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('170', plain,
% 1.29/1.48      (((v1_funct_1 @ 
% 1.29/1.48         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 1.29/1.48  thf('171', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('172', plain,
% 1.29/1.48      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48        (k1_zfmisc_1 @ 
% 1.29/1.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.48      inference('demod', [status(thm)], ['33', '71'])).
% 1.29/1.48  thf('173', plain,
% 1.29/1.48      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48        (k1_zfmisc_1 @ 
% 1.29/1.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.48      inference('demod', [status(thm)], ['79', '94'])).
% 1.29/1.48  thf('174', plain,
% 1.29/1.48      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.29/1.48         (~ (m1_subset_1 @ X21 @ 
% 1.29/1.48             (k1_zfmisc_1 @ 
% 1.29/1.48              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 1.29/1.48          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 1.29/1.48          | ~ (v1_funct_1 @ X21)
% 1.29/1.48          | ~ (m1_pre_topc @ X24 @ X25)
% 1.29/1.48          | (v2_struct_0 @ X24)
% 1.29/1.48          | ~ (m1_pre_topc @ X22 @ X25)
% 1.29/1.48          | (v2_struct_0 @ X22)
% 1.29/1.48          | ~ (l1_pre_topc @ X23)
% 1.29/1.48          | ~ (v2_pre_topc @ X23)
% 1.29/1.48          | (v2_struct_0 @ X23)
% 1.29/1.48          | ~ (l1_pre_topc @ X25)
% 1.29/1.48          | ~ (v2_pre_topc @ X25)
% 1.29/1.48          | (v2_struct_0 @ X25)
% 1.29/1.48          | ~ (v1_funct_1 @ X26)
% 1.29/1.48          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 1.29/1.48          | ~ (m1_subset_1 @ X26 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 1.29/1.48          | (v1_funct_2 @ (k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26) @ 
% 1.29/1.48             (u1_struct_0 @ (k1_tsep_1 @ X25 @ X22 @ X24)) @ 
% 1.29/1.48             (u1_struct_0 @ X23)))),
% 1.29/1.48      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 1.29/1.48  thf('175', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((v1_funct_2 @ 
% 1.29/1.48           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 1.29/1.48           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (m1_subset_1 @ X2 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X2)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.48          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 1.29/1.48          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('sup-', [status(thm)], ['173', '174'])).
% 1.29/1.48  thf('176', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('177', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('178', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 1.29/1.48      inference('demod', [status(thm)], ['119', '120'])).
% 1.29/1.48  thf('179', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((v1_funct_2 @ 
% 1.29/1.48           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 1.29/1.48           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (m1_subset_1 @ X2 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X2)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.48          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 1.29/1.48  thf('180', plain,
% 1.29/1.48      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['142', '143'])).
% 1.29/1.48  thf('181', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((v1_funct_2 @ 
% 1.29/1.48           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 1.29/1.48           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (m1_subset_1 @ X2 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X2)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.48      inference('demod', [status(thm)], ['179', '180'])).
% 1.29/1.48  thf('182', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ sk_D @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 1.29/1.48          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | (v1_funct_2 @ 
% 1.29/1.48             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('sup-', [status(thm)], ['172', '181'])).
% 1.29/1.48  thf('183', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 1.29/1.48      inference('demod', [status(thm)], ['153', '154'])).
% 1.29/1.48  thf('184', plain,
% 1.29/1.48      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['162', '163'])).
% 1.29/1.48  thf('185', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ sk_D @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | (v1_funct_2 @ 
% 1.29/1.48             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('demod', [status(thm)], ['182', '183', '184'])).
% 1.29/1.48  thf('186', plain,
% 1.29/1.48      (((v1_funct_2 @ 
% 1.29/1.48         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 1.29/1.48         (u1_struct_0 @ sk_B))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.48        | ~ (l1_pre_topc @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('sup-', [status(thm)], ['171', '185'])).
% 1.29/1.48  thf('187', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('188', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('190', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('191', plain,
% 1.29/1.48      (((v1_funct_2 @ 
% 1.29/1.48         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 1.29/1.48  thf('192', plain,
% 1.29/1.48      ((m1_subset_1 @ sk_E @ 
% 1.29/1.48        (k1_zfmisc_1 @ 
% 1.29/1.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('193', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf(t138_tmap_1, axiom,
% 1.29/1.48    (![A:$i]:
% 1.29/1.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.48       ( ![B:$i]:
% 1.29/1.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.29/1.48             ( l1_pre_topc @ B ) ) =>
% 1.29/1.48           ( ![C:$i]:
% 1.29/1.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.29/1.48               ( ![D:$i]:
% 1.29/1.48                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.29/1.48                   ( ![E:$i]:
% 1.29/1.48                     ( ( ( v1_funct_1 @ E ) & 
% 1.29/1.48                         ( v1_funct_2 @
% 1.29/1.48                           E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.29/1.48                           ( u1_struct_0 @ B ) ) & 
% 1.29/1.48                         ( m1_subset_1 @
% 1.29/1.48                           E @ 
% 1.29/1.48                           ( k1_zfmisc_1 @
% 1.29/1.48                             ( k2_zfmisc_1 @
% 1.29/1.48                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.29/1.48                               ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.29/1.48                       ( r2_funct_2 @
% 1.29/1.48                         ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 1.29/1.48                         ( u1_struct_0 @ B ) @ E @ 
% 1.29/1.48                         ( k10_tmap_1 @
% 1.29/1.48                           A @ B @ C @ D @ 
% 1.29/1.48                           ( k3_tmap_1 @
% 1.29/1.48                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 1.29/1.48                           ( k3_tmap_1 @
% 1.29/1.48                             A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.29/1.48  thf('194', plain,
% 1.29/1.48      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.29/1.48         ((v2_struct_0 @ X32)
% 1.29/1.48          | ~ (v2_pre_topc @ X32)
% 1.29/1.48          | ~ (l1_pre_topc @ X32)
% 1.29/1.48          | (v2_struct_0 @ X33)
% 1.29/1.48          | ~ (m1_pre_topc @ X33 @ X34)
% 1.29/1.48          | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ X34 @ X35 @ X33)) @ 
% 1.29/1.48             (u1_struct_0 @ X32) @ X36 @ 
% 1.29/1.48             (k10_tmap_1 @ X34 @ X32 @ X35 @ X33 @ 
% 1.29/1.48              (k3_tmap_1 @ X34 @ X32 @ (k1_tsep_1 @ X34 @ X35 @ X33) @ X35 @ 
% 1.29/1.48               X36) @ 
% 1.29/1.48              (k3_tmap_1 @ X34 @ X32 @ (k1_tsep_1 @ X34 @ X35 @ X33) @ X33 @ 
% 1.29/1.48               X36)))
% 1.29/1.48          | ~ (m1_subset_1 @ X36 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X34 @ X35 @ X33)) @ 
% 1.29/1.48                 (u1_struct_0 @ X32))))
% 1.29/1.48          | ~ (v1_funct_2 @ X36 @ 
% 1.29/1.48               (u1_struct_0 @ (k1_tsep_1 @ X34 @ X35 @ X33)) @ 
% 1.29/1.48               (u1_struct_0 @ X32))
% 1.29/1.48          | ~ (v1_funct_1 @ X36)
% 1.29/1.48          | ~ (m1_pre_topc @ X35 @ X34)
% 1.29/1.48          | (v2_struct_0 @ X35)
% 1.29/1.48          | ~ (l1_pre_topc @ X34)
% 1.29/1.48          | ~ (v2_pre_topc @ X34)
% 1.29/1.48          | (v2_struct_0 @ X34))),
% 1.29/1.48      inference('cnf', [status(esa)], [t138_tmap_1])).
% 1.29/1.48  thf('195', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i]:
% 1.29/1.48         (~ (m1_subset_1 @ X1 @ 
% 1.29/1.48             (k1_zfmisc_1 @ 
% 1.29/1.48              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 1.29/1.48          | (v2_struct_0 @ sk_A)
% 1.29/1.48          | ~ (v2_pre_topc @ sk_A)
% 1.29/1.48          | ~ (l1_pre_topc @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.29/1.48          | ~ (v1_funct_1 @ X1)
% 1.29/1.48          | ~ (v1_funct_2 @ X1 @ 
% 1.29/1.48               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 1.29/1.48               (u1_struct_0 @ X0))
% 1.29/1.48          | (r2_funct_2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ X0) @ X1 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ 
% 1.29/1.48              (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.29/1.48               sk_C @ X1) @ 
% 1.29/1.48              (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 1.29/1.48               sk_D @ X1)))
% 1.29/1.48          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0))),
% 1.29/1.48      inference('sup-', [status(thm)], ['193', '194'])).
% 1.29/1.48  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('198', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('199', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('200', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('201', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('202', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('203', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('204', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i]:
% 1.29/1.48         (~ (m1_subset_1 @ X1 @ 
% 1.29/1.48             (k1_zfmisc_1 @ 
% 1.29/1.48              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 1.29/1.48          | (v2_struct_0 @ sk_A)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (v1_funct_1 @ X1)
% 1.29/1.48          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 1.29/1.48          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ X0 @ sk_C @ sk_D @ 
% 1.29/1.48              (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_C @ X1) @ 
% 1.29/1.48              (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1)))
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0))),
% 1.29/1.48      inference('demod', [status(thm)],
% 1.29/1.48                ['195', '196', '197', '198', '199', '200', '201', '202', '203'])).
% 1.29/1.48  thf('205', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_B)
% 1.29/1.48        | ~ (v2_pre_topc @ sk_B)
% 1.29/1.48        | ~ (l1_pre_topc @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_D)
% 1.29/1.48        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.48           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 1.29/1.48            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))
% 1.29/1.48        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | ~ (v1_funct_1 @ sk_E)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_A))),
% 1.29/1.48      inference('sup-', [status(thm)], ['192', '204'])).
% 1.29/1.48  thf('206', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('207', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('208', plain,
% 1.29/1.48      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 1.29/1.48         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 1.29/1.48      inference('sup+', [status(thm)], ['86', '93'])).
% 1.29/1.48  thf('209', plain,
% 1.29/1.48      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 1.29/1.48         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 1.29/1.48      inference('sup+', [status(thm)], ['54', '70'])).
% 1.29/1.48  thf('210', plain,
% 1.29/1.48      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('211', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('212', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_D)
% 1.29/1.48        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.48           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_A))),
% 1.29/1.48      inference('demod', [status(thm)],
% 1.29/1.48                ['205', '206', '207', '208', '209', '210', '211'])).
% 1.29/1.48  thf('213', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('214', plain,
% 1.29/1.48      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48        (k1_zfmisc_1 @ 
% 1.29/1.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.48      inference('demod', [status(thm)], ['33', '71'])).
% 1.29/1.48  thf('215', plain,
% 1.29/1.48      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48        (k1_zfmisc_1 @ 
% 1.29/1.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.48      inference('demod', [status(thm)], ['79', '94'])).
% 1.29/1.48  thf('216', plain,
% 1.29/1.48      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.29/1.48         (~ (m1_subset_1 @ X21 @ 
% 1.29/1.48             (k1_zfmisc_1 @ 
% 1.29/1.48              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 1.29/1.48          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 1.29/1.48          | ~ (v1_funct_1 @ X21)
% 1.29/1.48          | ~ (m1_pre_topc @ X24 @ X25)
% 1.29/1.48          | (v2_struct_0 @ X24)
% 1.29/1.48          | ~ (m1_pre_topc @ X22 @ X25)
% 1.29/1.48          | (v2_struct_0 @ X22)
% 1.29/1.48          | ~ (l1_pre_topc @ X23)
% 1.29/1.48          | ~ (v2_pre_topc @ X23)
% 1.29/1.48          | (v2_struct_0 @ X23)
% 1.29/1.48          | ~ (l1_pre_topc @ X25)
% 1.29/1.48          | ~ (v2_pre_topc @ X25)
% 1.29/1.48          | (v2_struct_0 @ X25)
% 1.29/1.48          | ~ (v1_funct_1 @ X26)
% 1.29/1.48          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 1.29/1.48          | ~ (m1_subset_1 @ X26 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 1.29/1.48          | (m1_subset_1 @ (k10_tmap_1 @ X25 @ X23 @ X22 @ X24 @ X21 @ X26) @ 
% 1.29/1.48             (k1_zfmisc_1 @ 
% 1.29/1.48              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X25 @ X22 @ X24)) @ 
% 1.29/1.48               (u1_struct_0 @ X23)))))),
% 1.29/1.48      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 1.29/1.48  thf('217', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((m1_subset_1 @ 
% 1.29/1.48           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 1.29/1.48           (k1_zfmisc_1 @ 
% 1.29/1.48            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (m1_subset_1 @ X2 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X2)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (v2_pre_topc @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.48          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 1.29/1.48          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('sup-', [status(thm)], ['215', '216'])).
% 1.29/1.48  thf('218', plain, ((v2_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('219', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('220', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 1.29/1.48      inference('demod', [status(thm)], ['119', '120'])).
% 1.29/1.48  thf('221', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((m1_subset_1 @ 
% 1.29/1.48           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 1.29/1.48           (k1_zfmisc_1 @ 
% 1.29/1.48            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (m1_subset_1 @ X2 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X2)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1)
% 1.29/1.48          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 1.29/1.48  thf('222', plain,
% 1.29/1.48      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['142', '143'])).
% 1.29/1.48  thf('223', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.48         ((m1_subset_1 @ 
% 1.29/1.48           (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ X2) @ 
% 1.29/1.48           (k1_zfmisc_1 @ 
% 1.29/1.48            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (m1_subset_1 @ X2 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X2)
% 1.29/1.48          | (v2_struct_0 @ X1)
% 1.29/1.48          | ~ (v2_pre_topc @ X1)
% 1.29/1.48          | ~ (l1_pre_topc @ X1)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X1)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.29/1.48      inference('demod', [status(thm)], ['221', '222'])).
% 1.29/1.48  thf('224', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ sk_D @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 1.29/1.48          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | (m1_subset_1 @ 
% 1.29/1.48             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48             (k1_zfmisc_1 @ 
% 1.29/1.48              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 1.29/1.48               (u1_struct_0 @ sk_B)))))),
% 1.29/1.48      inference('sup-', [status(thm)], ['214', '223'])).
% 1.29/1.48  thf('225', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 1.29/1.48      inference('demod', [status(thm)], ['153', '154'])).
% 1.29/1.48  thf('226', plain,
% 1.29/1.48      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 1.29/1.48        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('clc', [status(thm)], ['162', '163'])).
% 1.29/1.48  thf('227', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (m1_pre_topc @ sk_D @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_D)
% 1.29/1.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.29/1.48          | (v2_struct_0 @ sk_C)
% 1.29/1.48          | (v2_struct_0 @ sk_B)
% 1.29/1.48          | ~ (l1_pre_topc @ X0)
% 1.29/1.48          | ~ (v2_pre_topc @ X0)
% 1.29/1.48          | (v2_struct_0 @ X0)
% 1.29/1.48          | (m1_subset_1 @ 
% 1.29/1.48             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48             (k1_zfmisc_1 @ 
% 1.29/1.48              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 1.29/1.48               (u1_struct_0 @ sk_B)))))),
% 1.29/1.48      inference('demod', [status(thm)], ['224', '225', '226'])).
% 1.29/1.48  thf('228', plain,
% 1.29/1.48      (((m1_subset_1 @ 
% 1.29/1.48         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48         (k1_zfmisc_1 @ 
% 1.29/1.48          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 1.29/1.48           (u1_struct_0 @ sk_B))))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.48        | ~ (l1_pre_topc @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('sup-', [status(thm)], ['213', '227'])).
% 1.29/1.48  thf('229', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('230', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('232', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('233', plain,
% 1.29/1.48      (((m1_subset_1 @ 
% 1.29/1.48         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48         (k1_zfmisc_1 @ 
% 1.29/1.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('demod', [status(thm)], ['228', '229', '230', '231', '232'])).
% 1.29/1.48  thf('234', plain,
% 1.29/1.48      ((m1_subset_1 @ sk_E @ 
% 1.29/1.48        (k1_zfmisc_1 @ 
% 1.29/1.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf(redefinition_r2_funct_2, axiom,
% 1.29/1.48    (![A:$i,B:$i,C:$i,D:$i]:
% 1.29/1.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.29/1.48         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.29/1.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.48       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.29/1.48  thf('235', plain,
% 1.29/1.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.29/1.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 1.29/1.48          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 1.29/1.48          | ~ (v1_funct_1 @ X0)
% 1.29/1.48          | ~ (v1_funct_1 @ X3)
% 1.29/1.48          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 1.29/1.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 1.29/1.48          | ((X0) = (X3))
% 1.29/1.48          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 1.29/1.48      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.29/1.48  thf('236', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.48             X0)
% 1.29/1.48          | ((sk_E) = (X0))
% 1.29/1.48          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X0)
% 1.29/1.48          | ~ (v1_funct_1 @ sk_E)
% 1.29/1.48          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 1.29/1.48      inference('sup-', [status(thm)], ['234', '235'])).
% 1.29/1.48  thf('237', plain, ((v1_funct_1 @ sk_E)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('238', plain,
% 1.29/1.48      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('239', plain,
% 1.29/1.48      (![X0 : $i]:
% 1.29/1.48         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.48             X0)
% 1.29/1.48          | ((sk_E) = (X0))
% 1.29/1.48          | ~ (m1_subset_1 @ X0 @ 
% 1.29/1.48               (k1_zfmisc_1 @ 
% 1.29/1.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.29/1.48          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48          | ~ (v1_funct_1 @ X0))),
% 1.29/1.48      inference('demod', [status(thm)], ['236', '237', '238'])).
% 1.29/1.48  thf('240', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | ~ (v1_funct_1 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | ~ (v1_funct_2 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | ((sk_E)
% 1.29/1.48            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.29/1.48      inference('sup-', [status(thm)], ['233', '239'])).
% 1.29/1.48  thf('241', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | ((sk_E)
% 1.29/1.48            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | ~ (v1_funct_2 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | ~ (v1_funct_1 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('sup-', [status(thm)], ['212', '240'])).
% 1.29/1.48  thf('242', plain,
% 1.29/1.48      ((~ (v1_funct_1 @ 
% 1.29/1.48           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | ~ (v1_funct_2 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 1.29/1.48             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | ((sk_E)
% 1.29/1.48            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_A))),
% 1.29/1.48      inference('simplify', [status(thm)], ['241'])).
% 1.29/1.48  thf('243', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | ((sk_E)
% 1.29/1.48            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | ~ (v1_funct_1 @ 
% 1.29/1.48             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.29/1.48      inference('sup-', [status(thm)], ['191', '242'])).
% 1.29/1.48  thf('244', plain,
% 1.29/1.48      ((~ (v1_funct_1 @ 
% 1.29/1.48           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | ((sk_E)
% 1.29/1.48            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('simplify', [status(thm)], ['243'])).
% 1.29/1.48  thf('245', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | ((sk_E)
% 1.29/1.48            = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 1.29/1.48      inference('sup-', [status(thm)], ['170', '244'])).
% 1.29/1.48  thf('246', plain,
% 1.29/1.48      ((((sk_E)
% 1.29/1.48          = (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('simplify', [status(thm)], ['245'])).
% 1.29/1.48  thf('247', plain,
% 1.29/1.48      (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.48          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 1.29/1.48          (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.48          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('248', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('249', plain,
% 1.29/1.48      (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.48          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.29/1.48          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 1.29/1.48           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 1.29/1.48           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 1.29/1.48      inference('demod', [status(thm)], ['247', '248'])).
% 1.29/1.48  thf('250', plain,
% 1.29/1.48      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.29/1.48           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_E)
% 1.29/1.48        | (v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_A))),
% 1.29/1.48      inference('sup-', [status(thm)], ['246', '249'])).
% 1.29/1.48  thf('251', plain,
% 1.29/1.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('sup-', [status(thm)], ['12', '250'])).
% 1.29/1.48  thf(fc2_struct_0, axiom,
% 1.29/1.48    (![A:$i]:
% 1.29/1.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.29/1.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.29/1.48  thf('252', plain,
% 1.29/1.48      (![X5 : $i]:
% 1.29/1.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 1.29/1.48          | ~ (l1_struct_0 @ X5)
% 1.29/1.48          | (v2_struct_0 @ X5))),
% 1.29/1.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.29/1.48  thf('253', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | ~ (l1_struct_0 @ sk_B))),
% 1.29/1.48      inference('sup-', [status(thm)], ['251', '252'])).
% 1.29/1.48  thf('254', plain, ((l1_pre_topc @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf(dt_l1_pre_topc, axiom,
% 1.29/1.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.29/1.48  thf('255', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.29/1.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.29/1.48  thf('256', plain, ((l1_struct_0 @ sk_B)),
% 1.29/1.48      inference('sup-', [status(thm)], ['254', '255'])).
% 1.29/1.48  thf('257', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_D)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B))),
% 1.29/1.48      inference('demod', [status(thm)], ['253', '256'])).
% 1.29/1.48  thf('258', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_A)
% 1.29/1.48        | (v2_struct_0 @ sk_B)
% 1.29/1.48        | (v2_struct_0 @ sk_C)
% 1.29/1.48        | (v2_struct_0 @ sk_D))),
% 1.29/1.48      inference('simplify', [status(thm)], ['257'])).
% 1.29/1.48  thf('259', plain, (~ (v2_struct_0 @ sk_B)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('260', plain,
% 1.29/1.48      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.29/1.48      inference('sup-', [status(thm)], ['258', '259'])).
% 1.29/1.48  thf('261', plain, (~ (v2_struct_0 @ sk_D)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('262', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.29/1.48      inference('clc', [status(thm)], ['260', '261'])).
% 1.29/1.48  thf('263', plain, (~ (v2_struct_0 @ sk_A)),
% 1.29/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.48  thf('264', plain, ((v2_struct_0 @ sk_C)),
% 1.29/1.48      inference('clc', [status(thm)], ['262', '263'])).
% 1.29/1.48  thf('265', plain, ($false), inference('demod', [status(thm)], ['0', '264'])).
% 1.29/1.48  
% 1.29/1.48  % SZS output end Refutation
% 1.29/1.48  
% 1.29/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
