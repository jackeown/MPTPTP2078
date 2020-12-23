%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r5ZEy7xlCB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:41 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  163 (1723 expanded)
%              Number of leaves         :   43 ( 525 expanded)
%              Depth                    :   27
%              Number of atoms          : 1489 (41834 expanded)
%              Number of equality atoms :   73 ( 948 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ( r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X29 @ X33 )
      | ( X29 != X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('28',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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

thf('42',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('44',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X23 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( ( g1_pre_topc @ X27 @ X28 )
       != ( g1_pre_topc @ X25 @ X26 ) )
      | ( X28 = X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
     != ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_pre_topc @ sk_B )
      = ( u1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('57',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X23 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( ( g1_pre_topc @ X27 @ X28 )
       != ( g1_pre_topc @ X25 @ X26 ) )
      | ( X27 = X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = X1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['53'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) )
     != ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('71',plain,
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

thf('72',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( ( k2_tmap_1 @ X37 @ X35 @ X38 @ X36 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) @ X38 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('78',plain,(
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
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
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
    inference('sup-',[status(thm)],['70','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k2_partfun1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

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
    inference(demod,[status(thm)],['79','80','81','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('92',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('93',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X39 @ X40 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('100',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('102',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['100','101'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('103',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k7_relat_1 @ X3 @ X4 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('106',plain,
    ( ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['68','111'])).

thf('113',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','112'])).

thf('114',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('117',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r5ZEy7xlCB
% 0.15/0.37  % Computer   : n018.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:58:12 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.25/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.54  % Solved by: fo/fo7.sh
% 0.25/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.54  % done 113 iterations in 0.051s
% 0.25/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.54  % SZS output start Refutation
% 0.25/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.54  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.25/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.25/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.25/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.54  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.25/0.54  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.25/0.54  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.25/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.25/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.25/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.25/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.25/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.25/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.54  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.25/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.54  thf(t60_tmap_1, conjecture,
% 0.25/0.54    (![A:$i]:
% 0.25/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.54       ( ![B:$i]:
% 0.25/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.54             ( l1_pre_topc @ B ) ) =>
% 0.25/0.54           ( ![C:$i]:
% 0.25/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.25/0.54               ( ![D:$i]:
% 0.25/0.54                 ( ( ( v1_funct_1 @ D ) & 
% 0.25/0.54                     ( v1_funct_2 @
% 0.25/0.54                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.54                     ( m1_subset_1 @
% 0.25/0.54                       D @ 
% 0.25/0.54                       ( k1_zfmisc_1 @
% 0.25/0.54                         ( k2_zfmisc_1 @
% 0.25/0.54                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.54                   ( ( ( g1_pre_topc @
% 0.25/0.54                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.25/0.54                       ( g1_pre_topc @
% 0.25/0.54                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.25/0.54                     ( r1_funct_2 @
% 0.25/0.54                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.25/0.54                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.25/0.54                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.54    (~( ![A:$i]:
% 0.25/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.54            ( l1_pre_topc @ A ) ) =>
% 0.25/0.54          ( ![B:$i]:
% 0.25/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.54                ( l1_pre_topc @ B ) ) =>
% 0.25/0.54              ( ![C:$i]:
% 0.25/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.25/0.54                  ( ![D:$i]:
% 0.25/0.54                    ( ( ( v1_funct_1 @ D ) & 
% 0.25/0.54                        ( v1_funct_2 @
% 0.25/0.54                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.54                        ( m1_subset_1 @
% 0.25/0.54                          D @ 
% 0.25/0.54                          ( k1_zfmisc_1 @
% 0.25/0.54                            ( k2_zfmisc_1 @
% 0.25/0.54                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.25/0.54                      ( ( ( g1_pre_topc @
% 0.25/0.54                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.25/0.54                          ( g1_pre_topc @
% 0.25/0.54                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.25/0.54                        ( r1_funct_2 @
% 0.25/0.54                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.25/0.54                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.25/0.54                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.54    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.25/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('1', plain,
% 0.25/0.54      ((m1_subset_1 @ sk_D @ 
% 0.25/0.54        (k1_zfmisc_1 @ 
% 0.25/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('2', plain,
% 0.25/0.54      ((m1_subset_1 @ sk_D @ 
% 0.25/0.54        (k1_zfmisc_1 @ 
% 0.25/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf(cc5_funct_2, axiom,
% 0.25/0.54    (![A:$i,B:$i]:
% 0.25/0.54     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.25/0.54       ( ![C:$i]:
% 0.25/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.54           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.25/0.54             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.25/0.54  thf('3', plain,
% 0.25/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.25/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.25/0.54          | (v1_partfun1 @ X11 @ X12)
% 0.25/0.54          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.25/0.54          | ~ (v1_funct_1 @ X11)
% 0.25/0.54          | (v1_xboole_0 @ X13))),
% 0.25/0.54      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.25/0.54  thf('4', plain,
% 0.25/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54        | ~ (v1_funct_1 @ sk_D)
% 0.25/0.54        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.25/0.54        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.25/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.54  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('6', plain,
% 0.25/0.54      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('7', plain,
% 0.25/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.25/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.25/0.54  thf(d4_partfun1, axiom,
% 0.25/0.54    (![A:$i,B:$i]:
% 0.25/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.25/0.54       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.25/0.54  thf('8', plain,
% 0.25/0.54      (![X14 : $i, X15 : $i]:
% 0.25/0.54         (~ (v1_partfun1 @ X15 @ X14)
% 0.25/0.54          | ((k1_relat_1 @ X15) = (X14))
% 0.25/0.54          | ~ (v4_relat_1 @ X15 @ X14)
% 0.25/0.54          | ~ (v1_relat_1 @ X15))),
% 0.25/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.25/0.54  thf('9', plain,
% 0.25/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54        | ~ (v1_relat_1 @ sk_D)
% 0.25/0.54        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.25/0.54        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.25/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.25/0.54  thf('10', plain,
% 0.25/0.54      ((m1_subset_1 @ sk_D @ 
% 0.25/0.54        (k1_zfmisc_1 @ 
% 0.25/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf(cc1_relset_1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i]:
% 0.25/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.54       ( v1_relat_1 @ C ) ))).
% 0.25/0.54  thf('11', plain,
% 0.25/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.54         ((v1_relat_1 @ X5)
% 0.25/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.25/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.25/0.54  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.25/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.54  thf('13', plain,
% 0.25/0.54      ((m1_subset_1 @ sk_D @ 
% 0.25/0.54        (k1_zfmisc_1 @ 
% 0.25/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf(cc2_relset_1, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i]:
% 0.25/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.25/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.25/0.54  thf('14', plain,
% 0.25/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.54         ((v4_relat_1 @ X8 @ X9)
% 0.25/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.25/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.25/0.54  thf('15', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.25/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.25/0.54  thf('16', plain,
% 0.25/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.25/0.54      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.25/0.54  thf(fc2_struct_0, axiom,
% 0.25/0.54    (![A:$i]:
% 0.25/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.25/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.25/0.54  thf('17', plain,
% 0.25/0.54      (![X24 : $i]:
% 0.25/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.25/0.54          | ~ (l1_struct_0 @ X24)
% 0.25/0.54          | (v2_struct_0 @ X24))),
% 0.25/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.25/0.54  thf('18', plain,
% 0.25/0.54      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))
% 0.25/0.54        | (v2_struct_0 @ sk_A)
% 0.25/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.25/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.25/0.54  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf(dt_l1_pre_topc, axiom,
% 0.25/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.25/0.54  thf('20', plain,
% 0.25/0.54      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.25/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.25/0.54  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.25/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.25/0.54  thf('22', plain,
% 0.25/0.54      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.25/0.54      inference('demod', [status(thm)], ['18', '21'])).
% 0.25/0.54  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('24', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.54  thf('25', plain,
% 0.25/0.54      ((m1_subset_1 @ sk_D @ 
% 0.25/0.54        (k1_zfmisc_1 @ 
% 0.25/0.54         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.54      inference('demod', [status(thm)], ['1', '24'])).
% 0.25/0.54  thf('26', plain,
% 0.25/0.54      ((m1_subset_1 @ sk_D @ 
% 0.25/0.54        (k1_zfmisc_1 @ 
% 0.25/0.54         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.54      inference('demod', [status(thm)], ['1', '24'])).
% 0.25/0.54  thf(redefinition_r1_funct_2, axiom,
% 0.25/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.25/0.54     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.25/0.54         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.25/0.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.25/0.54         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.25/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.25/0.54       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.25/0.54  thf('27', plain,
% 0.25/0.54      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.25/0.54         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.25/0.54          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.25/0.54          | ~ (v1_funct_1 @ X29)
% 0.25/0.54          | (v1_xboole_0 @ X32)
% 0.25/0.54          | (v1_xboole_0 @ X31)
% 0.25/0.54          | ~ (v1_funct_1 @ X33)
% 0.25/0.54          | ~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.25/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.25/0.54          | (r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X29 @ X33)
% 0.25/0.54          | ((X29) != (X33)))),
% 0.25/0.54      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.25/0.54  thf('28', plain,
% 0.25/0.54      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.25/0.54         ((r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X33 @ X33)
% 0.25/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.25/0.54          | ~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.25/0.54          | (v1_xboole_0 @ X31)
% 0.25/0.54          | (v1_xboole_0 @ X32)
% 0.25/0.54          | ~ (v1_funct_1 @ X33)
% 0.25/0.54          | ~ (v1_funct_2 @ X33 @ X30 @ X31)
% 0.25/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.25/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.25/0.54  thf('29', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i]:
% 0.25/0.54         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.25/0.54          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.25/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.25/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54          | (v1_xboole_0 @ X0)
% 0.25/0.54          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.25/0.54          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.25/0.54             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.25/0.54      inference('sup-', [status(thm)], ['26', '28'])).
% 0.25/0.54  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('31', plain,
% 0.25/0.54      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('32', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.54  thf('33', plain,
% 0.25/0.54      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.54  thf('34', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i]:
% 0.25/0.54         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.25/0.54          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.25/0.54          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54          | (v1_xboole_0 @ X0)
% 0.25/0.54          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.25/0.54             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.25/0.54      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.25/0.54  thf('35', plain,
% 0.25/0.54      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.54         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.25/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.54        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.25/0.54      inference('sup-', [status(thm)], ['25', '34'])).
% 0.25/0.54  thf('36', plain,
% 0.25/0.54      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.55  thf('37', plain,
% 0.25/0.55      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.25/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.25/0.55  thf('38', plain,
% 0.25/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.55        | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.25/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.25/0.55  thf('39', plain,
% 0.25/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.25/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('40', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('41', plain,
% 0.25/0.55      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.25/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.25/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.25/0.55  thf('42', plain,
% 0.25/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.25/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('43', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('44', plain,
% 0.25/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.25/0.55         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.25/0.55  thf('45', plain,
% 0.25/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.25/0.55         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.25/0.55  thf('46', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf(dt_u1_pre_topc, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( m1_subset_1 @
% 0.25/0.55         ( u1_pre_topc @ A ) @ 
% 0.25/0.55         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.25/0.55  thf('47', plain,
% 0.25/0.55      (![X23 : $i]:
% 0.25/0.55         ((m1_subset_1 @ (u1_pre_topc @ X23) @ 
% 0.25/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.25/0.55          | ~ (l1_pre_topc @ X23))),
% 0.25/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.25/0.55  thf(free_g1_pre_topc, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.25/0.55       ( ![C:$i,D:$i]:
% 0.25/0.55         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.25/0.55           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.25/0.55  thf('48', plain,
% 0.25/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.25/0.55         (((g1_pre_topc @ X27 @ X28) != (g1_pre_topc @ X25 @ X26))
% 0.25/0.55          | ((X28) = (X26))
% 0.25/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 0.25/0.55      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.25/0.55  thf('49', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.55         (~ (l1_pre_topc @ X0)
% 0.25/0.55          | ((u1_pre_topc @ X0) = (X1))
% 0.25/0.55          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.25/0.55              != (g1_pre_topc @ X2 @ X1)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.25/0.55  thf('50', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.25/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.25/0.55          | ((u1_pre_topc @ sk_B) = (X0))
% 0.25/0.55          | ~ (l1_pre_topc @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['46', '49'])).
% 0.25/0.55  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('52', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.25/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.25/0.55          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.25/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.25/0.55  thf('53', plain,
% 0.25/0.55      ((((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.25/0.55          != (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.25/0.55        | ((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['45', '52'])).
% 0.25/0.55  thf('54', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.25/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.25/0.55  thf('55', plain,
% 0.25/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.25/0.55         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C)))),
% 0.25/0.55      inference('demod', [status(thm)], ['44', '54'])).
% 0.25/0.55  thf('56', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('57', plain,
% 0.25/0.55      (![X23 : $i]:
% 0.25/0.55         ((m1_subset_1 @ (u1_pre_topc @ X23) @ 
% 0.25/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))
% 0.25/0.55          | ~ (l1_pre_topc @ X23))),
% 0.25/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.25/0.55  thf('58', plain,
% 0.25/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.25/0.55         (((g1_pre_topc @ X27 @ X28) != (g1_pre_topc @ X25 @ X26))
% 0.25/0.55          | ((X27) = (X25))
% 0.25/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 0.25/0.55      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.25/0.55  thf('59', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.55         (~ (l1_pre_topc @ X0)
% 0.25/0.55          | ((u1_struct_0 @ X0) = (X1))
% 0.25/0.55          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.25/0.55              != (g1_pre_topc @ X1 @ X2)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.25/0.55  thf('60', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.25/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.25/0.55          | ((u1_struct_0 @ sk_B) = (X1))
% 0.25/0.55          | ~ (l1_pre_topc @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['56', '59'])).
% 0.25/0.55  thf('61', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('63', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B))
% 0.25/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.25/0.55          | ((k1_relat_1 @ sk_D) = (X1)))),
% 0.25/0.55      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.25/0.55  thf('64', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.25/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.25/0.55  thf('65', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C))
% 0.25/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.25/0.55          | ((k1_relat_1 @ sk_D) = (X1)))),
% 0.25/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.25/0.55  thf('66', plain,
% 0.25/0.55      ((((g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C))
% 0.25/0.55          != (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_C)))
% 0.25/0.55        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['55', '65'])).
% 0.25/0.55  thf('67', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.25/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.25/0.55  thf('68', plain,
% 0.25/0.55      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.25/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.25/0.55      inference('demod', [status(thm)], ['41', '67'])).
% 0.25/0.55  thf('69', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('70', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_D @ 
% 0.25/0.55        (k1_zfmisc_1 @ 
% 0.25/0.55         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('demod', [status(thm)], ['1', '24'])).
% 0.25/0.55  thf('71', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf(d4_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.55             ( l1_pre_topc @ B ) ) =>
% 0.25/0.55           ( ![C:$i]:
% 0.25/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.25/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.55                 ( m1_subset_1 @
% 0.25/0.55                   C @ 
% 0.25/0.55                   ( k1_zfmisc_1 @
% 0.25/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.55               ( ![D:$i]:
% 0.25/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.25/0.55                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.25/0.55                     ( k2_partfun1 @
% 0.25/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.25/0.55                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('72', plain,
% 0.25/0.55      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.25/0.55         ((v2_struct_0 @ X35)
% 0.25/0.55          | ~ (v2_pre_topc @ X35)
% 0.25/0.55          | ~ (l1_pre_topc @ X35)
% 0.25/0.55          | ~ (m1_pre_topc @ X36 @ X37)
% 0.25/0.55          | ((k2_tmap_1 @ X37 @ X35 @ X38 @ X36)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35) @ 
% 0.25/0.55                 X38 @ (u1_struct_0 @ X36)))
% 0.25/0.55          | ~ (m1_subset_1 @ X38 @ 
% 0.25/0.55               (k1_zfmisc_1 @ 
% 0.25/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))))
% 0.25/0.55          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))
% 0.25/0.55          | ~ (v1_funct_1 @ X38)
% 0.25/0.55          | ~ (l1_pre_topc @ X37)
% 0.25/0.55          | ~ (v2_pre_topc @ X37)
% 0.25/0.55          | (v2_struct_0 @ X37))),
% 0.25/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.25/0.55  thf('73', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.25/0.55             (k1_zfmisc_1 @ 
% 0.25/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.25/0.55          | (v2_struct_0 @ sk_B)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.55          | ~ (v1_funct_1 @ X1)
% 0.25/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.25/0.55          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.25/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.25/0.55                 X1 @ (u1_struct_0 @ X2)))
% 0.25/0.55          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.25/0.55          | ~ (l1_pre_topc @ X0)
% 0.25/0.55          | ~ (v2_pre_topc @ X0)
% 0.25/0.55          | (v2_struct_0 @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.25/0.55  thf('74', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('76', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('77', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('78', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.25/0.55             (k1_zfmisc_1 @ 
% 0.25/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.25/0.55          | (v2_struct_0 @ sk_B)
% 0.25/0.55          | ~ (v1_funct_1 @ X1)
% 0.25/0.55          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.25/0.55          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.25/0.55              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.25/0.55                 (u1_struct_0 @ X2)))
% 0.25/0.55          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.25/0.55          | ~ (l1_pre_topc @ X0)
% 0.25/0.55          | ~ (v2_pre_topc @ X0)
% 0.25/0.55          | (v2_struct_0 @ X0))),
% 0.25/0.55      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.25/0.55  thf('79', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_A)
% 0.25/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.55          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.25/0.55              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.25/0.55          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.25/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.25/0.55          | (v2_struct_0 @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['70', '78'])).
% 0.25/0.55  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('82', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_D @ 
% 0.25/0.55        (k1_zfmisc_1 @ 
% 0.25/0.55         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('demod', [status(thm)], ['1', '24'])).
% 0.25/0.55  thf(redefinition_k2_partfun1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.25/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.25/0.55       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.25/0.55  thf('83', plain,
% 0.25/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.25/0.55          | ~ (v1_funct_1 @ X16)
% 0.25/0.55          | ((k2_partfun1 @ X17 @ X18 @ X16 @ X19) = (k7_relat_1 @ X16 @ X19)))),
% 0.25/0.55      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.25/0.55  thf('84', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.25/0.55            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.25/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.25/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.25/0.55  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('86', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ X0)
% 0.25/0.55           = (k7_relat_1 @ sk_D @ X0))),
% 0.25/0.55      inference('demod', [status(thm)], ['84', '85'])).
% 0.25/0.55  thf('87', plain,
% 0.25/0.55      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.55  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('89', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((v2_struct_0 @ sk_A)
% 0.25/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.25/0.55          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.25/0.55              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.25/0.55          | (v2_struct_0 @ sk_B))),
% 0.25/0.55      inference('demod', [status(thm)], ['79', '80', '81', '86', '87', '88'])).
% 0.25/0.55  thf('90', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_B)
% 0.25/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.25/0.55            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.25/0.55        | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['69', '89'])).
% 0.25/0.55  thf('91', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.25/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.25/0.55  thf('92', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t1_tsep_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.55           ( m1_subset_1 @
% 0.25/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.25/0.55  thf('93', plain,
% 0.25/0.55      (![X39 : $i, X40 : $i]:
% 0.25/0.55         (~ (m1_pre_topc @ X39 @ X40)
% 0.25/0.55          | (m1_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.25/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.25/0.55          | ~ (l1_pre_topc @ X40))),
% 0.25/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.25/0.55  thf('94', plain,
% 0.25/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.25/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.25/0.55  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('96', plain,
% 0.25/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.25/0.55  thf(t3_subset, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.55  thf('97', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.25/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.25/0.55  thf('98', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.25/0.55  thf('99', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('100', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.25/0.55      inference('demod', [status(thm)], ['98', '99'])).
% 0.25/0.55  thf('101', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.25/0.55      inference('simplify', [status(thm)], ['66'])).
% 0.25/0.55  thf('102', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))),
% 0.25/0.55      inference('demod', [status(thm)], ['100', '101'])).
% 0.25/0.55  thf(t97_relat_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ B ) =>
% 0.25/0.55       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.25/0.55         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.25/0.55  thf('103', plain,
% 0.25/0.55      (![X3 : $i, X4 : $i]:
% 0.25/0.55         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.25/0.55          | ((k7_relat_1 @ X3 @ X4) = (X3))
% 0.25/0.55          | ~ (v1_relat_1 @ X3))),
% 0.25/0.55      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.25/0.55  thf('104', plain,
% 0.25/0.55      ((~ (v1_relat_1 @ sk_D)
% 0.25/0.55        | ((k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (sk_D)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['102', '103'])).
% 0.25/0.55  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.25/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.55  thf('106', plain, (((k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (sk_D))),
% 0.25/0.55      inference('demod', [status(thm)], ['104', '105'])).
% 0.25/0.55  thf('107', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_B)
% 0.25/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.25/0.55        | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['90', '91', '106'])).
% 0.25/0.55  thf('108', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('109', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.25/0.55      inference('clc', [status(thm)], ['107', '108'])).
% 0.25/0.55  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('111', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.25/0.55      inference('clc', [status(thm)], ['109', '110'])).
% 0.25/0.55  thf('112', plain,
% 0.25/0.55      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.25/0.55          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.25/0.55      inference('demod', [status(thm)], ['68', '111'])).
% 0.25/0.55  thf('113', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['38', '112'])).
% 0.25/0.55  thf('114', plain,
% 0.25/0.55      (![X24 : $i]:
% 0.25/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.25/0.55          | ~ (l1_struct_0 @ X24)
% 0.25/0.55          | (v2_struct_0 @ X24))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.25/0.55  thf('115', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['113', '114'])).
% 0.25/0.55  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.25/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.25/0.55  thf('117', plain, ((v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('demod', [status(thm)], ['115', '116'])).
% 0.25/0.55  thf('118', plain, ($false), inference('demod', [status(thm)], ['0', '117'])).
% 0.25/0.55  
% 0.25/0.55  % SZS output end Refutation
% 0.25/0.55  
% 0.25/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
