%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dooKTRi56W

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:40 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  169 (1172 expanded)
%              Number of leaves         :   46 ( 365 expanded)
%              Depth                    :   27
%              Number of atoms          : 1477 (28051 expanded)
%              Number of equality atoms :   45 ( 547 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ( r1_funct_2 @ X31 @ X32 @ X35 @ X33 @ X30 @ X34 )
      | ( X30 != X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r1_funct_2 @ X31 @ X32 @ X35 @ X33 @ X34 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X33 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('39',plain,(
    ! [X6: $i] :
      ( ( ( k7_relat_1 @ X6 @ ( k1_relat_1 @ X6 ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('40',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('42',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('56',plain,(
    ! [X42: $i] :
      ( ( m1_pre_topc @ X42 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( m1_pre_topc @ X29 @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['55','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('65',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ ( g1_pre_topc @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) ) )
      | ( m1_pre_topc @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('69',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('79',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','81'])).

thf('83',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('86',plain,
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

thf('87',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X38 )
      | ( ( k2_tmap_1 @ X38 @ X36 @ X39 @ X37 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X36 ) @ X39 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('88',plain,(
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
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('93',plain,(
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
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
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
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('98',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k2_partfun1 @ X19 @ X20 @ X18 @ X21 )
        = ( k7_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96','101','102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','81'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['83','111'])).

thf('113',plain,
    ( ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('115',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','115'])).

thf('117',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('120',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['0','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dooKTRi56W
% 0.15/0.37  % Computer   : n018.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:26:27 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 191 iterations in 0.098s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.40/0.59  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.40/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(t60_tmap_1, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.59             ( l1_pre_topc @ B ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.40/0.59               ( ![D:$i]:
% 0.40/0.59                 ( ( ( v1_funct_1 @ D ) & 
% 0.40/0.59                     ( v1_funct_2 @
% 0.40/0.59                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.40/0.59                     ( m1_subset_1 @
% 0.40/0.59                       D @ 
% 0.40/0.59                       ( k1_zfmisc_1 @
% 0.40/0.59                         ( k2_zfmisc_1 @
% 0.40/0.59                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.40/0.59                   ( ( ( g1_pre_topc @
% 0.40/0.59                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.40/0.59                       ( g1_pre_topc @
% 0.40/0.59                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.40/0.59                     ( r1_funct_2 @
% 0.40/0.59                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.40/0.59                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.59            ( l1_pre_topc @ A ) ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.59                ( l1_pre_topc @ B ) ) =>
% 0.40/0.59              ( ![C:$i]:
% 0.40/0.59                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.40/0.59                  ( ![D:$i]:
% 0.40/0.59                    ( ( ( v1_funct_1 @ D ) & 
% 0.40/0.59                        ( v1_funct_2 @
% 0.40/0.59                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.40/0.59                        ( m1_subset_1 @
% 0.40/0.59                          D @ 
% 0.40/0.59                          ( k1_zfmisc_1 @
% 0.40/0.59                            ( k2_zfmisc_1 @
% 0.40/0.59                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.40/0.59                      ( ( ( g1_pre_topc @
% 0.40/0.59                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.40/0.59                          ( g1_pre_topc @
% 0.40/0.59                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.40/0.59                        ( r1_funct_2 @
% 0.40/0.59                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.40/0.59                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.40/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc5_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.59       ( ![C:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.40/0.59             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.40/0.59          | (v1_partfun1 @ X13 @ X14)
% 0.40/0.59          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.40/0.59          | ~ (v1_funct_1 @ X13)
% 0.40/0.59          | (v1_xboole_0 @ X15))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | ~ (v1_funct_1 @ sk_D)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.40/0.59  thf(d4_partfun1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.40/0.59       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (~ (v1_partfun1 @ X17 @ X16)
% 0.40/0.59          | ((k1_relat_1 @ X17) = (X16))
% 0.40/0.59          | ~ (v4_relat_1 @ X17 @ X16)
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_D)
% 0.40/0.59        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( v1_relat_1 @ C ) ))).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((v1_relat_1 @ X7)
% 0.40/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.59  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.59         ((v4_relat_1 @ X10 @ X11)
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.59  thf('15', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.40/0.59  thf(fc2_struct_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.59       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.40/0.59          | ~ (l1_struct_0 @ X25)
% 0.40/0.59          | (v2_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_l1_pre_topc, axiom,
% 0.40/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.59  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['18', '21'])).
% 0.40/0.59  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('24', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['1', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['1', '24'])).
% 0.40/0.59  thf(redefinition_r1_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.59     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.40/0.59         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.59         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.40/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.40/0.59       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.40/0.59          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.40/0.59          | ~ (v1_funct_1 @ X30)
% 0.40/0.59          | (v1_xboole_0 @ X33)
% 0.40/0.59          | (v1_xboole_0 @ X32)
% 0.40/0.59          | ~ (v1_funct_1 @ X34)
% 0.40/0.59          | ~ (v1_funct_2 @ X34 @ X35 @ X33)
% 0.40/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 0.40/0.59          | (r1_funct_2 @ X31 @ X32 @ X35 @ X33 @ X30 @ X34)
% 0.40/0.59          | ((X30) != (X34)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.40/0.59         ((r1_funct_2 @ X31 @ X32 @ X35 @ X33 @ X34 @ X34)
% 0.40/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 0.40/0.59          | ~ (v1_funct_2 @ X34 @ X35 @ X33)
% 0.40/0.59          | (v1_xboole_0 @ X32)
% 0.40/0.59          | (v1_xboole_0 @ X33)
% 0.40/0.59          | ~ (v1_funct_1 @ X34)
% 0.40/0.59          | ~ (v1_funct_2 @ X34 @ X31 @ X32)
% 0.40/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.40/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.40/0.59          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ sk_D)
% 0.40/0.59          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59          | (v1_xboole_0 @ X0)
% 0.40/0.59          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.40/0.59          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.40/0.59             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.59  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('32', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.40/0.59          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.40/0.59          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59          | (v1_xboole_0 @ X0)
% 0.40/0.59          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.40/0.59             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.40/0.59      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['25', '34'])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.40/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.59  thf(t98_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X6 : $i]:
% 0.40/0.59         (((k7_relat_1 @ X6 @ (k1_relat_1 @ X6)) = (X6)) | ~ (v1_relat_1 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.40/0.59          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('41', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.40/0.59          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t1_tsep_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.40/0.59           ( m1_subset_1 @
% 0.40/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X40 : $i, X41 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X40 @ X41)
% 0.40/0.59          | (m1_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.40/0.59          | ~ (l1_pre_topc @ X41))),
% 0.40/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.40/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.59  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.59  thf(t3_subset, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i]:
% 0.40/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('49', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.59  thf(d10_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i]:
% 0.40/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.40/0.59        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.59  thf('52', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('53', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.40/0.59        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.40/0.59  thf('55', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf(t2_tsep_1, axiom,
% 0.40/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X42 : $i]: ((m1_pre_topc @ X42 @ X42) | ~ (l1_pre_topc @ X42))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.40/0.59  thf(t65_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( l1_pre_topc @ B ) =>
% 0.40/0.59           ( ( m1_pre_topc @ A @ B ) <=>
% 0.40/0.59             ( m1_pre_topc @
% 0.40/0.59               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      (![X28 : $i, X29 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X28)
% 0.40/0.59          | ~ (m1_pre_topc @ X29 @ X28)
% 0.40/0.59          | (m1_pre_topc @ X29 @ 
% 0.40/0.59             (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 0.40/0.59          | ~ (l1_pre_topc @ X29))),
% 0.40/0.59      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | (m1_pre_topc @ X0 @ 
% 0.40/0.59             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.40/0.59          | ~ (l1_pre_topc @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((m1_pre_topc @ X0 @ 
% 0.40/0.59           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.40/0.59          | ~ (l1_pre_topc @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      (((m1_pre_topc @ sk_B @ 
% 0.40/0.59         (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['55', '59'])).
% 0.40/0.59  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      ((m1_pre_topc @ sk_B @ 
% 0.40/0.59        (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['60', '61'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.40/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('64', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.40/0.59         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['63', '64'])).
% 0.40/0.59  thf(t59_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_pre_topc @
% 0.40/0.59             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.40/0.59           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.40/0.59  thf('66', plain,
% 0.40/0.59      (![X26 : $i, X27 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X26 @ 
% 0.40/0.59             (g1_pre_topc @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27)))
% 0.40/0.59          | (m1_pre_topc @ X26 @ X27)
% 0.40/0.59          | ~ (l1_pre_topc @ X27))),
% 0.40/0.59      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.40/0.59  thf('67', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X0 @ 
% 0.40/0.59             (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.40/0.59          | ~ (l1_pre_topc @ sk_C)
% 0.40/0.59          | (m1_pre_topc @ X0 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.40/0.59  thf('68', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_m1_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X23 : $i, X24 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X23 @ X24)
% 0.40/0.59          | (l1_pre_topc @ X23)
% 0.40/0.59          | ~ (l1_pre_topc @ X24))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.40/0.59  thf('70', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('72', plain, ((l1_pre_topc @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['70', '71'])).
% 0.40/0.59  thf('73', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X0 @ 
% 0.40/0.59             (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.40/0.59          | (m1_pre_topc @ X0 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['67', '72'])).
% 0.40/0.59  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['62', '73'])).
% 0.40/0.59  thf('75', plain,
% 0.40/0.59      (![X40 : $i, X41 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X40 @ X41)
% 0.40/0.59          | (m1_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.40/0.59          | ~ (l1_pre_topc @ X41))),
% 0.40/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_C)
% 0.40/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.40/0.59  thf('77', plain, ((l1_pre_topc @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['70', '71'])).
% 0.40/0.59  thf('78', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('79', plain,
% 0.40/0.59      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ 
% 0.40/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i]:
% 0.40/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.59  thf('81', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.40/0.59  thf('82', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['54', '81'])).
% 0.40/0.59  thf('83', plain,
% 0.40/0.59      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.40/0.59          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '82'])).
% 0.40/0.59  thf('84', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['1', '24'])).
% 0.40/0.59  thf('86', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf(d4_tmap_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.59             ( l1_pre_topc @ B ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ![D:$i]:
% 0.40/0.59                 ( ( m1_pre_topc @ D @ A ) =>
% 0.40/0.59                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.40/0.59                     ( k2_partfun1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.40/0.59                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('87', plain,
% 0.40/0.59      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X36)
% 0.40/0.59          | ~ (v2_pre_topc @ X36)
% 0.40/0.59          | ~ (l1_pre_topc @ X36)
% 0.40/0.59          | ~ (m1_pre_topc @ X37 @ X38)
% 0.40/0.59          | ((k2_tmap_1 @ X38 @ X36 @ X39 @ X37)
% 0.40/0.59              = (k2_partfun1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X36) @ 
% 0.40/0.59                 X39 @ (u1_struct_0 @ X37)))
% 0.40/0.59          | ~ (m1_subset_1 @ X39 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X36))))
% 0.40/0.59          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X36))
% 0.40/0.59          | ~ (v1_funct_1 @ X39)
% 0.40/0.59          | ~ (l1_pre_topc @ X38)
% 0.40/0.59          | ~ (v2_pre_topc @ X38)
% 0.40/0.59          | (v2_struct_0 @ X38))),
% 0.40/0.59      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.40/0.59  thf('88', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X1 @ 
% 0.40/0.59             (k1_zfmisc_1 @ 
% 0.40/0.59              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.40/0.59          | (v2_struct_0 @ sk_B)
% 0.40/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.40/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.40/0.59          | ~ (v1_funct_1 @ X1)
% 0.40/0.59          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.40/0.59          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.40/0.59              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.40/0.59                 X1 @ (u1_struct_0 @ X2)))
% 0.40/0.59          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['86', '87'])).
% 0.40/0.59  thf('89', plain, ((v2_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('91', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('92', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['22', '23'])).
% 0.40/0.59  thf('93', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X1 @ 
% 0.40/0.59             (k1_zfmisc_1 @ 
% 0.40/0.59              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.40/0.59          | (v2_struct_0 @ sk_B)
% 0.40/0.59          | ~ (v1_funct_1 @ X1)
% 0.40/0.59          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.40/0.59          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.40/0.59              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.40/0.59                 (u1_struct_0 @ X2)))
% 0.40/0.59          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.40/0.59  thf('94', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.40/0.59          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.40/0.59              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59                 sk_D @ (u1_struct_0 @ X0)))
% 0.40/0.59          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.40/0.59          | ~ (v1_funct_1 @ sk_D)
% 0.40/0.59          | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['85', '93'])).
% 0.40/0.59  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('97', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_D @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['1', '24'])).
% 0.40/0.59  thf(redefinition_k2_partfun1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.40/0.59  thf('98', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.40/0.59          | ~ (v1_funct_1 @ X18)
% 0.40/0.59          | ((k2_partfun1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.40/0.59  thf('99', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.40/0.59            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('101', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ X0)
% 0.40/0.59           = (k7_relat_1 @ sk_D @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.40/0.59  thf('102', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('104', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.40/0.59          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.40/0.59              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.40/0.59          | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['94', '95', '96', '101', '102', '103'])).
% 0.40/0.59  thf('105', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.40/0.59            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.40/0.59        | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['84', '104'])).
% 0.40/0.59  thf('106', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['54', '81'])).
% 0.40/0.59  thf('107', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.40/0.59            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.40/0.59        | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['105', '106'])).
% 0.40/0.59  thf('108', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('109', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_A)
% 0.40/0.59        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.40/0.59            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 0.40/0.59      inference('clc', [status(thm)], ['107', '108'])).
% 0.40/0.59  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('111', plain,
% 0.40/0.59      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.40/0.59         = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.40/0.59      inference('clc', [status(thm)], ['109', '110'])).
% 0.40/0.59  thf('112', plain,
% 0.40/0.59      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.40/0.59          (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.40/0.59      inference('demod', [status(thm)], ['83', '111'])).
% 0.40/0.59  thf('113', plain,
% 0.40/0.59      ((~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.40/0.59        | ~ (v1_relat_1 @ sk_D))),
% 0.40/0.59      inference('sup-', [status(thm)], ['39', '112'])).
% 0.40/0.59  thf('114', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf('115', plain,
% 0.40/0.59      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.40/0.59      inference('demod', [status(thm)], ['113', '114'])).
% 0.40/0.59  thf('116', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['38', '115'])).
% 0.40/0.59  thf('117', plain,
% 0.40/0.59      (![X25 : $i]:
% 0.40/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.40/0.59          | ~ (l1_struct_0 @ X25)
% 0.40/0.59          | (v2_struct_0 @ X25))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.59  thf('118', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['116', '117'])).
% 0.40/0.59  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('120', plain, ((v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['118', '119'])).
% 0.40/0.59  thf('121', plain, ($false), inference('demod', [status(thm)], ['0', '120'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
