%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.os69Bzw6a6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:40 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  204 (2562 expanded)
%              Number of leaves         :   48 ( 777 expanded)
%              Depth                    :   28
%              Number of atoms          : 1743 (62540 expanded)
%              Number of equality atoms :   56 (1211 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t60_tmap_1,conjecture,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                   => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

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

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X28 @ X32 )
      | ( X28 != X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('37',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('41',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('57',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X45 ) @ ( u1_struct_0 @ X47 ) )
      | ( m1_pre_topc @ X45 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['60','61','62'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('64',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('67',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('73',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['65','70','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( X40
       != ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( m1_pre_topc @ X40 @ X42 )
      | ( m1_pre_topc @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('77',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ( m1_pre_topc @ X41 @ X42 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) @ X42 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) ) @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('89',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('92',plain,(
    ! [X27: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('93',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['78','89','90','96','97','98','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['74','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('103',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('107',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('108',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','110'])).

thf('112',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

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

thf('116',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( ( k2_tmap_1 @ X36 @ X34 @ X37 @ X35 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) @ X37 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('127',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k2_partfun1 @ X20 @ X21 @ X19 @ X22 )
        = ( k7_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('132',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125','130','131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','110'])).

thf('136',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('137',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k7_relat_1 @ X6 @ X7 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('140',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','110'])).

thf('142',plain,
    ( ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['112','147'])).

thf('149',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','148'])).

thf('150',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('153',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['0','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.os69Bzw6a6
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:18:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 340 iterations in 0.211s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.68  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.68  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.68  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.45/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.45/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.68  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.68  thf(t60_tmap_1, conjecture,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.68             ( l1_pre_topc @ B ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.45/0.68               ( ![D:$i]:
% 0.45/0.68                 ( ( ( v1_funct_1 @ D ) & 
% 0.45/0.68                     ( v1_funct_2 @
% 0.45/0.68                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.68                     ( m1_subset_1 @
% 0.45/0.68                       D @ 
% 0.45/0.68                       ( k1_zfmisc_1 @
% 0.45/0.68                         ( k2_zfmisc_1 @
% 0.45/0.68                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.45/0.68                   ( ( ( g1_pre_topc @
% 0.45/0.68                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.45/0.68                       ( g1_pre_topc @
% 0.45/0.68                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.45/0.68                     ( r1_funct_2 @
% 0.45/0.68                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.45/0.68                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i]:
% 0.45/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.68            ( l1_pre_topc @ A ) ) =>
% 0.45/0.68          ( ![B:$i]:
% 0.45/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.68                ( l1_pre_topc @ B ) ) =>
% 0.45/0.68              ( ![C:$i]:
% 0.45/0.68                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.45/0.68                  ( ![D:$i]:
% 0.45/0.68                    ( ( ( v1_funct_1 @ D ) & 
% 0.45/0.68                        ( v1_funct_2 @
% 0.45/0.68                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.45/0.68                        ( m1_subset_1 @
% 0.45/0.68                          D @ 
% 0.45/0.68                          ( k1_zfmisc_1 @
% 0.45/0.68                            ( k2_zfmisc_1 @
% 0.45/0.68                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.45/0.68                      ( ( ( g1_pre_topc @
% 0.45/0.68                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.45/0.68                          ( g1_pre_topc @
% 0.45/0.68                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.45/0.68                        ( r1_funct_2 @
% 0.45/0.68                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.45/0.68                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.45/0.68  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc5_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.68       ( ![C:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.68             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.45/0.68          | (v1_partfun1 @ X14 @ X15)
% 0.45/0.68          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.45/0.68          | ~ (v1_funct_1 @ X14)
% 0.45/0.68          | (v1_xboole_0 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ~ (v1_funct_1 @ sk_D)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.68  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.68  thf(d4_partfun1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.68       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i]:
% 0.45/0.68         (~ (v1_partfun1 @ X18 @ X17)
% 0.45/0.68          | ((k1_relat_1 @ X18) = (X17))
% 0.45/0.68          | ~ (v4_relat_1 @ X18 @ X17)
% 0.45/0.68          | ~ (v1_relat_1 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_D)
% 0.45/0.68        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( v1_relat_1 @ C ) ))).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.68         ((v1_relat_1 @ X8)
% 0.45/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.68  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc2_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.68         ((v4_relat_1 @ X11 @ X12)
% 0.45/0.68          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.68  thf('15', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.45/0.68  thf(fc2_struct_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.68       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X26 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.45/0.68          | ~ (l1_struct_0 @ X26)
% 0.45/0.68          | (v2_struct_0 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_l1_pre_topc, axiom,
% 0.45/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.68  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['18', '21'])).
% 0.45/0.68  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('24', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['1', '24'])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['1', '24'])).
% 0.45/0.68  thf(redefinition_r1_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.68     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.45/0.68         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.68         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.45/0.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.68       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.45/0.68          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.45/0.68          | ~ (v1_funct_1 @ X28)
% 0.45/0.68          | (v1_xboole_0 @ X31)
% 0.45/0.68          | (v1_xboole_0 @ X30)
% 0.45/0.68          | ~ (v1_funct_1 @ X32)
% 0.45/0.68          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.45/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.45/0.68          | (r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X28 @ X32)
% 0.45/0.68          | ((X28) != (X32)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.68         ((r1_funct_2 @ X29 @ X30 @ X33 @ X31 @ X32 @ X32)
% 0.45/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 0.45/0.68          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 0.45/0.68          | (v1_xboole_0 @ X30)
% 0.45/0.68          | (v1_xboole_0 @ X31)
% 0.45/0.68          | ~ (v1_funct_1 @ X32)
% 0.45/0.68          | ~ (v1_funct_2 @ X32 @ X29 @ X30)
% 0.45/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['27'])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.45/0.68          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ sk_D)
% 0.45/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (v1_xboole_0 @ X0)
% 0.45/0.68          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.45/0.68      inference('sup-', [status(thm)], ['26', '28'])).
% 0.45/0.68  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('32', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.45/0.68          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.45/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (v1_xboole_0 @ X0)
% 0.45/0.68          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.45/0.68             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['25', '34'])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.45/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.45/0.68          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('40', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.45/0.68          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.68  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t1_tsep_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.68           ( m1_subset_1 @
% 0.45/0.68             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (![X43 : $i, X44 : $i]:
% 0.45/0.68         (~ (m1_pre_topc @ X43 @ X44)
% 0.45/0.68          | (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.45/0.68          | ~ (l1_pre_topc @ X44))),
% 0.45/0.68      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      ((~ (l1_pre_topc @ sk_B)
% 0.45/0.68        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.68  thf(t3_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]:
% 0.45/0.68         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('48', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.68  thf(d10_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.68  thf('49', plain,
% 0.45/0.68      (![X0 : $i, X2 : $i]:
% 0.45/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.45/0.68        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.68  thf('51', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('52', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      ((~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.45/0.68        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.45/0.68  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.68  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.68      inference('simplify', [status(thm)], ['55'])).
% 0.45/0.68  thf(t4_tsep_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( m1_pre_topc @ C @ A ) =>
% 0.45/0.68               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.45/0.68                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.45/0.68         (~ (m1_pre_topc @ X45 @ X46)
% 0.45/0.68          | ~ (r1_tarski @ (u1_struct_0 @ X45) @ (u1_struct_0 @ X47))
% 0.45/0.68          | (m1_pre_topc @ X45 @ X47)
% 0.45/0.68          | ~ (m1_pre_topc @ X47 @ X46)
% 0.45/0.68          | ~ (l1_pre_topc @ X46)
% 0.45/0.68          | ~ (v2_pre_topc @ X46))),
% 0.45/0.68      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (v2_pre_topc @ X1)
% 0.45/0.68          | ~ (l1_pre_topc @ X1)
% 0.45/0.68          | ~ (m1_pre_topc @ X0 @ X1)
% 0.45/0.68          | (m1_pre_topc @ X0 @ X0)
% 0.45/0.68          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((m1_pre_topc @ X0 @ X0)
% 0.45/0.68          | ~ (m1_pre_topc @ X0 @ X1)
% 0.45/0.68          | ~ (l1_pre_topc @ X1)
% 0.45/0.68          | ~ (v2_pre_topc @ X1))),
% 0.45/0.68      inference('simplify', [status(thm)], ['58'])).
% 0.45/0.68  thf('60', plain,
% 0.45/0.68      ((~ (v2_pre_topc @ sk_B)
% 0.45/0.68        | ~ (l1_pre_topc @ sk_B)
% 0.45/0.68        | (m1_pre_topc @ sk_C @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['54', '59'])).
% 0.45/0.68  thf('61', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.45/0.68  thf(t11_tmap_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.45/0.68           ( ( v1_pre_topc @
% 0.45/0.68               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.45/0.68             ( m1_pre_topc @
% 0.45/0.68               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.45/0.68  thf('64', plain,
% 0.45/0.68      (![X38 : $i, X39 : $i]:
% 0.45/0.68         (~ (m1_pre_topc @ X38 @ X39)
% 0.45/0.68          | (m1_pre_topc @ 
% 0.45/0.68             (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)) @ X39)
% 0.45/0.68          | ~ (l1_pre_topc @ X39))),
% 0.45/0.69      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      ((~ (l1_pre_topc @ sk_C)
% 0.45/0.69        | (m1_pre_topc @ 
% 0.45/0.69           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.69  thf('66', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(dt_m1_pre_topc, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_pre_topc @ A ) =>
% 0.45/0.69       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (![X24 : $i, X25 : $i]:
% 0.45/0.69         (~ (m1_pre_topc @ X24 @ X25)
% 0.45/0.69          | (l1_pre_topc @ X24)
% 0.45/0.69          | ~ (l1_pre_topc @ X25))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.69  thf('68', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.69  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('70', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.69      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.45/0.69         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('72', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('73', plain,
% 0.45/0.69      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.45/0.69         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['71', '72'])).
% 0.45/0.69  thf('74', plain,
% 0.45/0.69      ((m1_pre_topc @ 
% 0.45/0.69        (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)) @ sk_C)),
% 0.45/0.69      inference('demod', [status(thm)], ['65', '70', '73'])).
% 0.45/0.69  thf('75', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf(t12_tmap_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_pre_topc @ A ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.45/0.69               ( ( ( B ) =
% 0.45/0.69                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.45/0.69                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.45/0.69         (~ (v2_pre_topc @ X40)
% 0.45/0.69          | ~ (l1_pre_topc @ X40)
% 0.45/0.69          | ((X40) != (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.45/0.69          | ~ (m1_pre_topc @ X40 @ X42)
% 0.45/0.69          | (m1_pre_topc @ X41 @ X42)
% 0.45/0.69          | ~ (l1_pre_topc @ X41)
% 0.45/0.69          | ~ (v2_pre_topc @ X41)
% 0.45/0.69          | ~ (l1_pre_topc @ X42))),
% 0.45/0.69      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.45/0.69  thf('77', plain,
% 0.45/0.69      (![X41 : $i, X42 : $i]:
% 0.45/0.69         (~ (l1_pre_topc @ X42)
% 0.45/0.69          | ~ (v2_pre_topc @ X41)
% 0.45/0.69          | ~ (l1_pre_topc @ X41)
% 0.45/0.69          | (m1_pre_topc @ X41 @ X42)
% 0.45/0.69          | ~ (m1_pre_topc @ 
% 0.45/0.69               (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)) @ X42)
% 0.45/0.69          | ~ (l1_pre_topc @ 
% 0.45/0.69               (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.45/0.69          | ~ (v2_pre_topc @ 
% 0.45/0.69               (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41))))),
% 0.45/0.69      inference('simplify', [status(thm)], ['76'])).
% 0.45/0.69  thf('78', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l1_pre_topc @ 
% 0.45/0.69             (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.45/0.69          | ~ (v2_pre_topc @ 
% 0.45/0.69               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.45/0.69          | ~ (m1_pre_topc @ 
% 0.45/0.69               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.45/0.69          | (m1_pre_topc @ sk_B @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.69          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['75', '77'])).
% 0.45/0.69  thf('79', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('80', plain,
% 0.45/0.69      (![X38 : $i, X39 : $i]:
% 0.45/0.69         (~ (m1_pre_topc @ X38 @ X39)
% 0.45/0.69          | (m1_pre_topc @ 
% 0.45/0.69             (g1_pre_topc @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38)) @ X39)
% 0.45/0.69          | ~ (l1_pre_topc @ X39))),
% 0.45/0.69      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.45/0.69  thf('81', plain,
% 0.45/0.69      ((~ (l1_pre_topc @ sk_B)
% 0.45/0.69        | (m1_pre_topc @ 
% 0.45/0.69           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['79', '80'])).
% 0.45/0.69  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('83', plain,
% 0.45/0.69      ((m1_pre_topc @ 
% 0.45/0.69        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B)),
% 0.45/0.69      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.69  thf('84', plain,
% 0.45/0.69      (![X24 : $i, X25 : $i]:
% 0.45/0.69         (~ (m1_pre_topc @ X24 @ X25)
% 0.45/0.69          | (l1_pre_topc @ X24)
% 0.45/0.69          | ~ (l1_pre_topc @ X25))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.69  thf('85', plain,
% 0.45/0.69      ((~ (l1_pre_topc @ sk_B)
% 0.45/0.69        | (l1_pre_topc @ 
% 0.45/0.69           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.69  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('87', plain,
% 0.45/0.69      ((l1_pre_topc @ 
% 0.45/0.69        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['85', '86'])).
% 0.45/0.69  thf('88', plain,
% 0.45/0.69      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.45/0.69         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['71', '72'])).
% 0.45/0.69  thf('89', plain,
% 0.45/0.69      ((l1_pre_topc @ 
% 0.45/0.69        (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['87', '88'])).
% 0.45/0.69  thf('90', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('91', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf(fc6_pre_topc, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69       ( ( v1_pre_topc @
% 0.45/0.69           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.45/0.69         ( v2_pre_topc @
% 0.45/0.69           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.45/0.69  thf('92', plain,
% 0.45/0.69      (![X27 : $i]:
% 0.45/0.69         ((v2_pre_topc @ 
% 0.45/0.69           (g1_pre_topc @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27)))
% 0.45/0.69          | ~ (l1_pre_topc @ X27)
% 0.45/0.69          | ~ (v2_pre_topc @ X27))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.45/0.69  thf('93', plain,
% 0.45/0.69      (((v2_pre_topc @ 
% 0.45/0.69         (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.45/0.69        | ~ (v2_pre_topc @ sk_B)
% 0.45/0.69        | ~ (l1_pre_topc @ sk_B))),
% 0.45/0.69      inference('sup+', [status(thm)], ['91', '92'])).
% 0.45/0.69  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('96', plain,
% 0.45/0.69      ((v2_pre_topc @ 
% 0.45/0.69        (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.45/0.69      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.45/0.69  thf('97', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('99', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('100', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (m1_pre_topc @ 
% 0.45/0.69             (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.45/0.69          | (m1_pre_topc @ sk_B @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('demod', [status(thm)],
% 0.45/0.69                ['78', '89', '90', '96', '97', '98', '99'])).
% 0.45/0.69  thf('101', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['74', '100'])).
% 0.45/0.69  thf('102', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.69      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.69  thf('103', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.45/0.69      inference('demod', [status(thm)], ['101', '102'])).
% 0.45/0.69  thf('104', plain,
% 0.45/0.69      (![X43 : $i, X44 : $i]:
% 0.45/0.69         (~ (m1_pre_topc @ X43 @ X44)
% 0.45/0.69          | (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 0.45/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.45/0.69          | ~ (l1_pre_topc @ X44))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.45/0.69  thf('105', plain,
% 0.45/0.69      ((~ (l1_pre_topc @ sk_C)
% 0.45/0.69        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['103', '104'])).
% 0.45/0.69  thf('106', plain, ((l1_pre_topc @ sk_C)),
% 0.45/0.69      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.69  thf('107', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('108', plain,
% 0.45/0.69      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ 
% 0.45/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.45/0.69  thf('109', plain,
% 0.45/0.69      (![X3 : $i, X4 : $i]:
% 0.45/0.69         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('110', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['108', '109'])).
% 0.45/0.69  thf('111', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['53', '110'])).
% 0.45/0.69  thf('112', plain,
% 0.45/0.69      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.69          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.45/0.69          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['41', '111'])).
% 0.45/0.69  thf('113', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('114', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_D @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '24'])).
% 0.45/0.69  thf('115', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf(d4_tmap_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.69             ( l1_pre_topc @ B ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.69                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.69                 ( m1_subset_1 @
% 0.45/0.69                   C @ 
% 0.45/0.69                   ( k1_zfmisc_1 @
% 0.45/0.69                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.69               ( ![D:$i]:
% 0.45/0.69                 ( ( m1_pre_topc @ D @ A ) =>
% 0.45/0.69                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.45/0.69                     ( k2_partfun1 @
% 0.45/0.69                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.45/0.69                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('116', plain,
% 0.45/0.69      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.69         ((v2_struct_0 @ X34)
% 0.45/0.69          | ~ (v2_pre_topc @ X34)
% 0.45/0.69          | ~ (l1_pre_topc @ X34)
% 0.45/0.69          | ~ (m1_pre_topc @ X35 @ X36)
% 0.45/0.69          | ((k2_tmap_1 @ X36 @ X34 @ X37 @ X35)
% 0.45/0.69              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34) @ 
% 0.45/0.69                 X37 @ (u1_struct_0 @ X35)))
% 0.45/0.69          | ~ (m1_subset_1 @ X37 @ 
% 0.45/0.69               (k1_zfmisc_1 @ 
% 0.45/0.69                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))))
% 0.45/0.69          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X34))
% 0.45/0.69          | ~ (v1_funct_1 @ X37)
% 0.45/0.69          | ~ (l1_pre_topc @ X36)
% 0.45/0.69          | ~ (v2_pre_topc @ X36)
% 0.45/0.69          | (v2_struct_0 @ X36))),
% 0.45/0.69      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.45/0.69  thf('117', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.69             (k1_zfmisc_1 @ 
% 0.45/0.69              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.45/0.69          | (v2_struct_0 @ sk_B)
% 0.45/0.69          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.69          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.69          | ~ (v1_funct_1 @ X1)
% 0.45/0.69          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.45/0.69          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.45/0.69              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.45/0.69                 X1 @ (u1_struct_0 @ X2)))
% 0.45/0.69          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | (v2_struct_0 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['115', '116'])).
% 0.45/0.69  thf('118', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('120', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('121', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.45/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('122', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.69             (k1_zfmisc_1 @ 
% 0.45/0.69              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.45/0.69          | (v2_struct_0 @ sk_B)
% 0.45/0.69          | ~ (v1_funct_1 @ X1)
% 0.45/0.69          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.45/0.69          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.45/0.69              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.45/0.69                 (u1_struct_0 @ X2)))
% 0.45/0.69          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | (v2_struct_0 @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 0.45/0.69  thf('123', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.69          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.45/0.69          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.45/0.69              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.69                 sk_D @ (u1_struct_0 @ X0)))
% 0.45/0.69          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.45/0.69          | ~ (v1_funct_1 @ sk_D)
% 0.45/0.69          | (v2_struct_0 @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['114', '122'])).
% 0.45/0.69  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('126', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_D @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.69      inference('demod', [status(thm)], ['1', '24'])).
% 0.45/0.69  thf(redefinition_k2_partfun1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.69       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.45/0.69  thf('127', plain,
% 0.45/0.69      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.45/0.69          | ~ (v1_funct_1 @ X19)
% 0.45/0.69          | ((k2_partfun1 @ X20 @ X21 @ X19 @ X22) = (k7_relat_1 @ X19 @ X22)))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.45/0.69  thf('128', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.45/0.69            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.45/0.69          | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.69      inference('sup-', [status(thm)], ['126', '127'])).
% 0.45/0.69  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('130', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ X0)
% 0.45/0.69           = (k7_relat_1 @ sk_D @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['128', '129'])).
% 0.45/0.69  thf('131', plain,
% 0.45/0.69      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.69  thf('132', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('133', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v2_struct_0 @ sk_A)
% 0.45/0.69          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.45/0.69          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.45/0.69              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.45/0.69          | (v2_struct_0 @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)],
% 0.45/0.69                ['123', '124', '125', '130', '131', '132'])).
% 0.45/0.69  thf('134', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_B)
% 0.45/0.69        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.45/0.69            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['113', '133'])).
% 0.45/0.69  thf('135', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['53', '110'])).
% 0.45/0.69  thf('136', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['108', '109'])).
% 0.45/0.69  thf(t97_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.45/0.69         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.45/0.69  thf('137', plain,
% 0.45/0.69      (![X6 : $i, X7 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.45/0.69          | ((k7_relat_1 @ X6 @ X7) = (X6))
% 0.45/0.69          | ~ (v1_relat_1 @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.45/0.69  thf('138', plain,
% 0.45/0.69      ((~ (v1_relat_1 @ sk_D)
% 0.45/0.69        | ((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['136', '137'])).
% 0.45/0.69  thf('139', plain, ((v1_relat_1 @ sk_D)),
% 0.45/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.69  thf('140', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.45/0.69      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.69  thf('141', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['53', '110'])).
% 0.45/0.69  thf('142', plain, (((k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (sk_D))),
% 0.45/0.69      inference('demod', [status(thm)], ['140', '141'])).
% 0.45/0.69  thf('143', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_B)
% 0.45/0.69        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.45/0.69        | (v2_struct_0 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['134', '135', '142'])).
% 0.45/0.69  thf('144', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('145', plain,
% 0.45/0.69      (((v2_struct_0 @ sk_A)
% 0.45/0.69        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.45/0.69      inference('clc', [status(thm)], ['143', '144'])).
% 0.45/0.69  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('147', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.45/0.69      inference('clc', [status(thm)], ['145', '146'])).
% 0.45/0.69  thf('148', plain,
% 0.45/0.69      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.69          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.45/0.69      inference('demod', [status(thm)], ['112', '147'])).
% 0.45/0.69  thf('149', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['38', '148'])).
% 0.45/0.69  thf('150', plain,
% 0.45/0.69      (![X26 : $i]:
% 0.45/0.69         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.45/0.69          | ~ (l1_struct_0 @ X26)
% 0.45/0.69          | (v2_struct_0 @ X26))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.69  thf('151', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['149', '150'])).
% 0.45/0.69  thf('152', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.69      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.69  thf('153', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.69      inference('demod', [status(thm)], ['151', '152'])).
% 0.45/0.69  thf('154', plain, ($false), inference('demod', [status(thm)], ['0', '153'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
