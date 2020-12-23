%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nMfgmePgOz

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 285 expanded)
%              Number of leaves         :   39 (  98 expanded)
%              Depth                    :   25
%              Number of atoms          : 1394 (5675 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t109_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                     => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t109_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r1_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r2_hidden @ X27 @ X25 )
      | ( r1_tmap_1 @ X26 @ ( k6_tmap_1 @ X26 @ X25 ) @ ( k7_tmap_1 @ X26 @ X25 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t108_tmap_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D @ sk_B_2 )
    | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_D )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t64_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ( X33 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X30 )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('45',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('53',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('61',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('69',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','50','58','66','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B_2 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B_2 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r2_hidden @ sk_D @ sk_B_2 )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('85',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('86',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r2_hidden @ sk_D @ sk_B_2 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    r2_hidden @ sk_D @ sk_B_2 ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['8','96'])).

thf(rc4_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc4_struct_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('99',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('103',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['104','105'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('107',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('108',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['101','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','111'])).

thf('113',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc4_struct_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('116',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['0','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nMfgmePgOz
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 127 iterations in 0.061s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(t109_tmap_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.20/0.52                 ( ![D:$i]:
% 0.20/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.52                     ( r1_tmap_1 @
% 0.20/0.52                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.20/0.52                       ( k2_tmap_1 @
% 0.20/0.52                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.20/0.52                       D ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.52                  ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.20/0.52                    ( ![D:$i]:
% 0.20/0.52                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.52                        ( r1_tmap_1 @
% 0.20/0.52                          C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.20/0.52                          ( k2_tmap_1 @
% 0.20/0.52                            A @ ( k6_tmap_1 @ A @ B ) @ 
% 0.20/0.52                            ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.20/0.52                          D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t109_tmap_1])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d1_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf('2', plain, ((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ sk_B_2)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t2_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((r2_hidden @ X7 @ X8)
% 0.20/0.52          | (v1_xboole_0 @ X8)
% 0.20/0.52          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.52        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(t3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.52          | ~ (r2_hidden @ X5 @ X6)
% 0.20/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.52          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.20/0.52          | ~ (r2_hidden @ sk_D @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_D @ sk_B_2) | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.52  thf('9', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t55_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.52               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X16)
% 0.20/0.52          | ~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.52          | (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.20/0.52          | ~ (l1_pre_topc @ X17)
% 0.20/0.52          | (v2_struct_0 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C_1)
% 0.20/0.52        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_C_1)
% 0.20/0.52        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A) | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t108_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.20/0.52                 ( r1_tmap_1 @
% 0.20/0.52                   A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.52          | (r2_hidden @ X27 @ X25)
% 0.20/0.52          | (r1_tmap_1 @ X26 @ (k6_tmap_1 @ X26 @ X25) @ 
% 0.20/0.52             (k7_tmap_1 @ X26 @ X25) @ X27)
% 0.20/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.20/0.52          | ~ (l1_pre_topc @ X26)
% 0.20/0.52          | ~ (v2_pre_topc @ X26)
% 0.20/0.52          | (v2_struct_0 @ X26))),
% 0.20/0.52      inference('cnf', [status(esa)], [t108_tmap_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52             (k7_tmap_1 @ sk_A @ sk_B_2) @ X0)
% 0.20/0.52          | (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52             (k7_tmap_1 @ sk_A @ sk_B_2) @ X0)
% 0.20/0.52          | (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((r2_hidden @ sk_D @ sk_B_2)
% 0.20/0.52        | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52           (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_D)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '26'])).
% 0.20/0.52  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52         (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_D)
% 0.20/0.52        | (r2_hidden @ sk_D @ sk_B_2))),
% 0.20/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k7_tmap_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.20/0.52         ( v1_funct_2 @
% 0.20/0.52           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.52           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( m1_subset_1 @
% 0.20/0.52           ( k7_tmap_1 @ A @ B ) @ 
% 0.20/0.52           ( k1_zfmisc_1 @
% 0.20/0.52             ( k2_zfmisc_1 @
% 0.20/0.52               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21)
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | (m1_subset_1 @ (k7_tmap_1 @ X21 @ X22) @ 
% 0.20/0.52             (k1_zfmisc_1 @ 
% 0.20/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ 
% 0.20/0.52               (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52         (k1_zfmisc_1 @ 
% 0.20/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52         (k1_zfmisc_1 @ 
% 0.20/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))))
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.52  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52        (k1_zfmisc_1 @ 
% 0.20/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))))),
% 0.20/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf(t64_tmap_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.52             ( l1_pre_topc @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.52                 ( m1_subset_1 @
% 0.20/0.52                   C @ 
% 0.20/0.52                   ( k1_zfmisc_1 @
% 0.20/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.52                       ( ![F:$i]:
% 0.20/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.52                           ( ( ( ( E ) = ( F ) ) & 
% 0.20/0.52                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.20/0.52                             ( r1_tmap_1 @
% 0.20/0.52                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X28)
% 0.20/0.52          | ~ (v2_pre_topc @ X28)
% 0.20/0.52          | ~ (l1_pre_topc @ X28)
% 0.20/0.52          | (v2_struct_0 @ X29)
% 0.20/0.52          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.52          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.20/0.52          | ((X33) != (X30))
% 0.20/0.52          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X33)
% 0.20/0.52          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.20/0.52          | ~ (m1_subset_1 @ X32 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.20/0.52          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.20/0.52          | ~ (v1_funct_1 @ X32)
% 0.20/0.52          | ~ (l1_pre_topc @ X31)
% 0.20/0.52          | ~ (v2_pre_topc @ X31)
% 0.20/0.52          | (v2_struct_0 @ X31))),
% 0.20/0.52      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X31)
% 0.20/0.52          | ~ (v2_pre_topc @ X31)
% 0.20/0.52          | ~ (l1_pre_topc @ X31)
% 0.20/0.52          | ~ (v1_funct_1 @ X32)
% 0.20/0.52          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.20/0.52          | ~ (m1_subset_1 @ X32 @ 
% 0.20/0.52               (k1_zfmisc_1 @ 
% 0.20/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.20/0.52          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X30)
% 0.20/0.52          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.52          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.52          | (v2_struct_0 @ X29)
% 0.20/0.52          | ~ (l1_pre_topc @ X28)
% 0.20/0.52          | ~ (v2_pre_topc @ X28)
% 0.20/0.52          | (v2_struct_0 @ X28))),
% 0.20/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.20/0.52             X1)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52               (k7_tmap_1 @ sk_A @ sk_B_2) @ X1)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52               (u1_struct_0 @ sk_A) @ 
% 0.20/0.52               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.20/0.52          | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.52  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21)
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | (v1_funct_2 @ (k7_tmap_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.20/0.52             (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.20/0.52  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))),
% 0.20/0.52      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X21)
% 0.20/0.52          | ~ (v2_pre_topc @ X21)
% 0.20/0.52          | (v2_struct_0 @ X21)
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.52          | (v1_funct_1 @ (k7_tmap_1 @ X21 @ X22)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.52  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('58', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2))),
% 0.20/0.52      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k6_tmap_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.52         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.52         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X19)
% 0.20/0.52          | ~ (v2_pre_topc @ X19)
% 0.20/0.52          | (v2_struct_0 @ X19)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.52          | (l1_pre_topc @ (k6_tmap_1 @ X19 @ X20)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.20/0.52  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('66', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 0.20/0.52      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X19)
% 0.20/0.52          | ~ (v2_pre_topc @ X19)
% 0.20/0.52          | (v2_struct_0 @ X19)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.52          | (v2_pre_topc @ (k6_tmap_1 @ X19 @ X20)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.52  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('74', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 0.20/0.52      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.20/0.52             X1)
% 0.20/0.52          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52               (k7_tmap_1 @ sk_A @ sk_B_2) @ X1)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))),
% 0.20/0.52      inference('demod', [status(thm)],
% 0.20/0.52                ['40', '41', '42', '50', '58', '66', '74'])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ sk_D @ sk_B_2)
% 0.20/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.20/0.52             sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '75'])).
% 0.20/0.52  thf('77', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ sk_D @ sk_B_2)
% 0.20/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.20/0.52             sk_D)
% 0.20/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ X0)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_C_1)
% 0.20/0.52        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.52        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52            (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_C_1) @ 
% 0.20/0.52           sk_D)
% 0.20/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52        | (r2_hidden @ sk_D @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '78'])).
% 0.20/0.52  thf('80', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_C_1)
% 0.20/0.52        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52            (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_C_1) @ 
% 0.20/0.52           sk_D)
% 0.20/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52        | (r2_hidden @ sk_D @ sk_B_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain,
% 0.20/0.52      (~ (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52          (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.20/0.52           (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_C_1) @ 
% 0.20/0.52          sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      (((r2_hidden @ sk_D @ sk_B_2)
% 0.20/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52        | (v2_struct_0 @ sk_C_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(fc4_tmap_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( ( ~( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.20/0.52         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X23)
% 0.20/0.52          | ~ (v2_pre_topc @ X23)
% 0.20/0.52          | (v2_struct_0 @ X23)
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.52          | ~ (v2_struct_0 @ (k6_tmap_1 @ X23 @ X24)))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc4_tmap_1])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.52  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.20/0.52  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('91', plain, (~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 0.20/0.52      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v2_struct_0 @ sk_C_1)
% 0.20/0.52        | (r2_hidden @ sk_D @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '91'])).
% 0.20/0.52  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('94', plain, (((r2_hidden @ sk_D @ sk_B_2) | (v2_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.52  thf('95', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('96', plain, ((r2_hidden @ sk_D @ sk_B_2)),
% 0.20/0.52      inference('clc', [status(thm)], ['94', '95'])).
% 0.20/0.52  thf('97', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '96'])).
% 0.20/0.52  thf(rc4_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ?[B:$i]:
% 0.20/0.52         ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.52           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('98', plain,
% 0.20/0.52      (![X15 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_B_1 @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.52          | ~ (l1_struct_0 @ X15)
% 0.20/0.52          | (v2_struct_0 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc4_struct_0])).
% 0.20/0.52  thf(t5_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.52          | ~ (v1_xboole_0 @ X11)
% 0.20/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.52  thf('100', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v2_struct_0 @ X0)
% 0.20/0.52          | ~ (l1_struct_0 @ X0)
% 0.20/0.52          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.52          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.52  thf('101', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_C_1))
% 0.20/0.52          | ~ (l1_struct_0 @ sk_C_1)
% 0.20/0.52          | (v2_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['97', '100'])).
% 0.20/0.52  thf('102', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.52          | (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('104', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.52  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('106', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.52  thf(dt_l1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('108', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_C_1)) | (v2_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['101', '108'])).
% 0.20/0.52  thf('110', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('111', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_C_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['109', '110'])).
% 0.20/0.52  thf('112', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '111'])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      (![X15 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (sk_B_1 @ X15))
% 0.20/0.52          | ~ (l1_struct_0 @ X15)
% 0.20/0.52          | (v2_struct_0 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [rc4_struct_0])).
% 0.20/0.52  thf('114', plain, (((v2_struct_0 @ sk_C_1) | ~ (l1_struct_0 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['112', '113'])).
% 0.20/0.52  thf('115', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.52  thf('116', plain, ((v2_struct_0 @ sk_C_1)),
% 0.20/0.52      inference('demod', [status(thm)], ['114', '115'])).
% 0.20/0.52  thf('117', plain, ($false), inference('demod', [status(thm)], ['0', '116'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
