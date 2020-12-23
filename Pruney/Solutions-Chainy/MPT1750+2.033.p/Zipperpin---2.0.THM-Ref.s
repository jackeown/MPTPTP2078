%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mo1TfLTp8M

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  149 (1299 expanded)
%              Number of leaves         :   41 ( 402 expanded)
%              Depth                    :   28
%              Number of atoms          : 1393 (30146 expanded)
%              Number of equality atoms :   59 ( 642 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( v1_partfun1 @ X8 @ X9 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X10 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_partfun1 @ X12 @ X11 )
      | ( ( k1_relat_1 @ X12 )
        = X11 )
      | ~ ( v4_relat_1 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14','17'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','26'])).

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

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( r1_funct_2 @ X25 @ X26 @ X29 @ X27 @ X24 @ X28 )
      | ( X24 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r1_funct_2 @ X25 @ X26 @ X29 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('39',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( ( ( k7_relat_1 @ X4 @ ( k1_relat_1 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('42',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('44',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('47',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X18 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('51',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( g1_pre_topc @ X22 @ X23 )
       != ( g1_pre_topc @ X20 @ X21 ) )
      | ( X23 = X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
     != ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_pre_topc @ sk_B )
      = ( u1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','57'])).

thf('59',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('60',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['56'])).

thf('61',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( g1_pre_topc @ X22 @ X23 )
       != ( g1_pre_topc @ X20 @ X21 ) )
      | ( X22 = X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = X0 )
      | ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) )
     != ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','26'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

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

thf('70',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( ( k2_tmap_1 @ X32 @ X30 @ X33 @ X31 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ X33 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('76',plain,(
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
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
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
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k2_partfun1 @ X14 @ X15 @ X13 @ X16 )
        = ( k7_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['64'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['66','96'])).

thf('98',plain,
    ( ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('100',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','100'])).

thf('102',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('105',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mo1TfLTp8M
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 89 iterations in 0.047s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(t60_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.51                     ( v1_funct_2 @
% 0.21/0.51                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                     ( m1_subset_1 @
% 0.21/0.51                       D @ 
% 0.21/0.51                       ( k1_zfmisc_1 @
% 0.21/0.51                         ( k2_zfmisc_1 @
% 0.21/0.51                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51                   ( ( ( g1_pre_topc @
% 0.21/0.51                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.21/0.51                       ( g1_pre_topc @
% 0.21/0.51                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.51                     ( r1_funct_2 @
% 0.21/0.51                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.51                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.21/0.51                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51                ( l1_pre_topc @ B ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.51                        ( v1_funct_2 @
% 0.21/0.51                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                        ( m1_subset_1 @
% 0.21/0.51                          D @ 
% 0.21/0.51                          ( k1_zfmisc_1 @
% 0.21/0.51                            ( k2_zfmisc_1 @
% 0.21/0.51                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51                      ( ( ( g1_pre_topc @
% 0.21/0.51                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.21/0.51                          ( g1_pre_topc @
% 0.21/0.51                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.51                        ( r1_funct_2 @
% 0.21/0.51                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.51                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.21/0.51                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc5_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.51             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.21/0.51          | (v1_partfun1 @ X8 @ X9)
% 0.21/0.51          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.21/0.51          | ~ (v1_funct_1 @ X8)
% 0.21/0.51          | (v1_xboole_0 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.51  thf(d4_partfun1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v1_partfun1 @ X12 @ X11)
% 0.21/0.51          | ((k1_relat_1 @ X12) = (X11))
% 0.21/0.51          | ~ (v4_relat_1 @ X12 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_D)
% 0.21/0.51        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.51          | (v1_relat_1 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ 
% 0.21/0.51           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.21/0.51        | (v1_relat_1 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf(fc6_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.51  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X5 @ X6)
% 0.21/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('17', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['9', '14', '17'])).
% 0.21/0.51  thf(fc2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X19 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.21/0.51          | ~ (l1_struct_0 @ X19)
% 0.21/0.51          | (v2_struct_0 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '23'])).
% 0.21/0.51  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '26'])).
% 0.21/0.51  thf(redefinition_r1_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.51         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.21/0.51         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.21/0.51       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.51          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.21/0.51          | ~ (v1_funct_1 @ X24)
% 0.21/0.51          | (v1_xboole_0 @ X27)
% 0.21/0.51          | (v1_xboole_0 @ X26)
% 0.21/0.51          | ~ (v1_funct_1 @ X28)
% 0.21/0.51          | ~ (v1_funct_2 @ X28 @ X29 @ X27)
% 0.21/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.21/0.51          | (r1_funct_2 @ X25 @ X26 @ X29 @ X27 @ X24 @ X28)
% 0.21/0.51          | ((X24) != (X28)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.51         ((r1_funct_2 @ X25 @ X26 @ X29 @ X27 @ X28 @ X28)
% 0.21/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.21/0.51          | ~ (v1_funct_2 @ X28 @ X29 @ X27)
% 0.21/0.51          | (v1_xboole_0 @ X26)
% 0.21/0.51          | (v1_xboole_0 @ X27)
% 0.21/0.51          | ~ (v1_funct_1 @ X28)
% 0.21/0.51          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 0.21/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.21/0.51             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.51  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.21/0.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (v1_xboole_0 @ X0)
% 0.21/0.51          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.21/0.51             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.21/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.51  thf(t98_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X4 : $i]:
% 0.21/0.51         (((k7_relat_1 @ X4 @ (k1_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.51          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('43', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.51          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('46', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.51         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.51         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('49', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf(dt_u1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( u1_pre_topc @ A ) @ 
% 0.21/0.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X18 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (u1_pre_topc @ X18) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf(free_g1_pre_topc, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( ![C:$i,D:$i]:
% 0.21/0.51         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.51           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (((g1_pre_topc @ X22 @ X23) != (g1_pre_topc @ X20 @ X21))
% 0.21/0.51          | ((X23) = (X21))
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.21/0.51      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((u1_pre_topc @ sk_B) = (X0))
% 0.21/0.51          | ((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.21/0.51              != (g1_pre_topc @ X1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.21/0.51          != (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.21/0.51        | ((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '55'])).
% 0.21/0.51  thf('57', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.21/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.51         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('60', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.21/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D))))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (((g1_pre_topc @ X22 @ X23) != (g1_pre_topc @ X20 @ X21))
% 0.21/0.51          | ((X22) = (X20))
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.21/0.51      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ sk_D) = (X0))
% 0.21/0.51          | ((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C))
% 0.21/0.51              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C))
% 0.21/0.51          != (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C)))
% 0.21/0.51        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '63'])).
% 0.21/0.51  thf('65', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.21/0.51      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.51          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '65'])).
% 0.21/0.51  thf('67', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['1', '26'])).
% 0.21/0.51  thf('69', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf(d4_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.51                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.51                     ( k2_partfun1 @
% 0.21/0.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.51                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X30)
% 0.21/0.51          | ~ (v2_pre_topc @ X30)
% 0.21/0.51          | ~ (l1_pre_topc @ X30)
% 0.21/0.51          | ~ (m1_pre_topc @ X31 @ X32)
% 0.21/0.51          | ((k2_tmap_1 @ X32 @ X30 @ X33 @ X31)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 0.21/0.51                 X33 @ (u1_struct_0 @ X31)))
% 0.21/0.51          | ~ (m1_subset_1 @ X33 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 0.21/0.51          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 0.21/0.51          | ~ (v1_funct_1 @ X33)
% 0.21/0.51          | ~ (l1_pre_topc @ X32)
% 0.21/0.51          | ~ (v2_pre_topc @ X32)
% 0.21/0.51          | (v2_struct_0 @ X32))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.21/0.51          | (v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ X1)
% 0.21/0.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.21/0.51                 X1 @ (u1_struct_0 @ X2)))
% 0.21/0.51          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('72', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('74', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('75', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.21/0.51          | (v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ X1)
% 0.21/0.51          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.21/0.51              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.21/0.51                 (u1_struct_0 @ X2)))
% 0.21/0.51          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.21/0.51              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                 sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '76'])).
% 0.21/0.51  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.51          | ~ (v1_funct_1 @ X13)
% 0.21/0.51          | ((k2_partfun1 @ X14 @ X15 @ X13 @ X16) = (k7_relat_1 @ X13 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.51            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.51  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.51           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('85', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ X0)
% 0.21/0.51           = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.51          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.21/0.51              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['77', '78', '79', '86', '87', '88'])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.51            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '89'])).
% 0.21/0.51  thf('91', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.21/0.51      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.51            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.51  thf('93', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.51            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 0.21/0.51      inference('clc', [status(thm)], ['92', '93'])).
% 0.21/0.51  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.51         = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.51          (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['66', '96'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      ((~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '97'])).
% 0.21/0.51  thf('99', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.51  thf('101', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (![X19 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.21/0.51          | ~ (l1_struct_0 @ X19)
% 0.21/0.51          | (v2_struct_0 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('103', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.51  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['103', '104'])).
% 0.21/0.51  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
