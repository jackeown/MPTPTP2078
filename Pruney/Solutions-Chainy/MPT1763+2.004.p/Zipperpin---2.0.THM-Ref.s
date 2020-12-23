%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L6WzgskRIz

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 864 expanded)
%              Number of leaves         :   39 ( 273 expanded)
%              Depth                    :   23
%              Number of atoms          : 1279 (17256 expanded)
%              Number of equality atoms :   42 ( 139 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t74_tmap_1,conjecture,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

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
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_tmap_1])).

thf('0',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','11','14'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

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

thf('29',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) )
      | ( m1_pre_topc @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['9','10'])).

thf('36',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('38',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['9','10'])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('42',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ sk_C @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

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

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X28 )
      | ( ( k3_tmap_1 @ X27 @ X25 @ X28 @ X26 @ X29 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) @ X29 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_C @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_C )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tmap_1 @ X2 @ X0 @ sk_C @ X3 @ X1 )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_pre_topc @ X3 @ sk_C )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k2_partfun1 @ X16 @ X17 @ X15 @ X18 )
        = ( k7_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60','67','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','72'])).

thf('74',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('75',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('77',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_D )
        = sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_D )
        = sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
    = sk_D ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('90',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_funct_2 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('98',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['24','87','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L6WzgskRIz
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:39:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 67 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(t74_tmap_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48             ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.48                     ( v1_funct_2 @
% 0.20/0.48                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.48                     ( m1_subset_1 @
% 0.20/0.48                       D @ 
% 0.20/0.48                       ( k1_zfmisc_1 @
% 0.20/0.48                         ( k2_zfmisc_1 @
% 0.20/0.48                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.48                   ( r2_funct_2 @
% 0.20/0.48                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.48                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48                ( l1_pre_topc @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.48                  ( ![D:$i]:
% 0.20/0.48                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.48                        ( v1_funct_2 @
% 0.20/0.48                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.48                        ( m1_subset_1 @
% 0.20/0.48                          D @ 
% 0.20/0.48                          ( k1_zfmisc_1 @
% 0.20/0.48                            ( k2_zfmisc_1 @
% 0.20/0.48                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.48                      ( r2_funct_2 @
% 0.20/0.48                        ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.48                        ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t74_tmap_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.48          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc5_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.48             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.20/0.48          | (v1_partfun1 @ X10 @ X11)
% 0.20/0.48          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | (v1_xboole_0 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.48        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.48        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.48        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.48  thf(d4_partfun1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.48       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (v1_partfun1 @ X14 @ X13)
% 0.20/0.48          | ((k1_relat_1 @ X14) = (X13))
% 0.20/0.48          | ~ (v4_relat_1 @ X14 @ X13)
% 0.20/0.48          | ~ (v1_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_D)
% 0.20/0.48        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.20/0.48        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('11', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((v4_relat_1 @ X7 @ X8)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.48  thf('14', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.48        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '11', '14'])).
% 0.20/0.48  thf(fc2_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X24 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.20/0.48          | ~ (l1_struct_0 @ X24)
% 0.20/0.48          | (v2_struct_0 @ X24))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))
% 0.20/0.48        | (v2_struct_0 @ sk_B)
% 0.20/0.48        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.48  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.48  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (~ (r2_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.48          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '23'])).
% 0.20/0.48  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('28', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf(t4_tsep_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.48               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.48                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X30 @ X31)
% 0.20/0.48          | ~ (r1_tarski @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32))
% 0.20/0.48          | (m1_pre_topc @ X30 @ X32)
% 0.20/0.48          | ~ (m1_pre_topc @ X32 @ X31)
% 0.20/0.48          | ~ (l1_pre_topc @ X31)
% 0.20/0.48          | ~ (v2_pre_topc @ X31))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (v2_pre_topc @ X1)
% 0.20/0.48          | ~ (l1_pre_topc @ X1)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.48          | (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | (m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.48  thf('32', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf(t209_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X0) = (k7_relat_1 @ X0 @ X1))
% 0.20/0.48          | ~ (v4_relat_1 @ X0 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.48        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('36', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf(t87_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X3)) @ X3)
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.48      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('42', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | (m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | (m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '44'])).
% 0.20/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf(d5_tmap_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48             ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.48                   ( ![E:$i]:
% 0.20/0.48                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.48                         ( v1_funct_2 @
% 0.20/0.48                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.48                         ( m1_subset_1 @
% 0.20/0.48                           E @ 
% 0.20/0.48                           ( k1_zfmisc_1 @
% 0.20/0.48                             ( k2_zfmisc_1 @
% 0.20/0.48                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.48                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.48                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.48                           ( k2_partfun1 @
% 0.20/0.48                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.48                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X25)
% 0.20/0.48          | ~ (v2_pre_topc @ X25)
% 0.20/0.48          | ~ (l1_pre_topc @ X25)
% 0.20/0.48          | ~ (m1_pre_topc @ X26 @ X27)
% 0.20/0.48          | ~ (m1_pre_topc @ X26 @ X28)
% 0.20/0.48          | ((k3_tmap_1 @ X27 @ X25 @ X28 @ X26 @ X29)
% 0.20/0.48              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25) @ 
% 0.20/0.48                 X29 @ (u1_struct_0 @ X26)))
% 0.20/0.48          | ~ (m1_subset_1 @ X29 @ 
% 0.20/0.48               (k1_zfmisc_1 @ 
% 0.20/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))))
% 0.20/0.48          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))
% 0.20/0.48          | ~ (v1_funct_1 @ X29)
% 0.20/0.48          | ~ (m1_pre_topc @ X28 @ X27)
% 0.20/0.48          | ~ (l1_pre_topc @ X27)
% 0.20/0.48          | ~ (v2_pre_topc @ X27)
% 0.20/0.48          | (v2_struct_0 @ X27))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.20/0.48          | (v2_struct_0 @ X2)
% 0.20/0.48          | ~ (v2_pre_topc @ X2)
% 0.20/0.48          | ~ (l1_pre_topc @ X2)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.20/0.48          | ((k3_tmap_1 @ X2 @ X0 @ sk_C @ X3 @ X1)
% 0.20/0.48              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.20/0.48                 X1 @ (u1_struct_0 @ X3)))
% 0.20/0.48          | ~ (m1_pre_topc @ X3 @ sk_C)
% 0.20/0.48          | ~ (m1_pre_topc @ X3 @ X2)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('56', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.20/0.48          | (v2_struct_0 @ X2)
% 0.20/0.48          | ~ (v2_pre_topc @ X2)
% 0.20/0.48          | ~ (l1_pre_topc @ X2)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.20/0.48          | ~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.20/0.48          | ((k3_tmap_1 @ X2 @ X0 @ sk_C @ X3 @ X1)
% 0.20/0.48              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.20/0.48                 (u1_struct_0 @ X3)))
% 0.20/0.48          | ~ (m1_pre_topc @ X3 @ sk_C)
% 0.20/0.48          | ~ (m1_pre_topc @ X3 @ X2)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.20/0.48              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48                 sk_D @ (u1_struct_0 @ X1)))
% 0.20/0.48          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '57'])).
% 0.20/0.48  thf('59', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k2_partfun1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.20/0.48          | ~ (v1_funct_1 @ X15)
% 0.20/0.48          | ((k2_partfun1 @ X16 @ X17 @ X15 @ X18) = (k7_relat_1 @ X15 @ X18)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.48            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.48           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.48  thf('66', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_D @ X0)
% 0.20/0.48           = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('69', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.20/0.48              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X1)))
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['58', '59', '60', '67', '70', '71'])).
% 0.20/0.48  thf('73', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_D)
% 0.20/0.48              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '72'])).
% 0.20/0.48  thf('74', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('75', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('76', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('77', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['78'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '79'])).
% 0.20/0.48  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.20/0.48  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_B)
% 0.20/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D)))),
% 0.20/0.48      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.48  thf('86', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('87', plain, (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))),
% 0.20/0.48      inference('clc', [status(thm)], ['85', '86'])).
% 0.20/0.48  thf('88', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('89', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_D @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf(reflexivity_r2_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.20/0.48  thf('90', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.48         ((r2_funct_2 @ X19 @ X20 @ X21 @ X21)
% 0.20/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.48          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.20/0.48          | ~ (v1_funct_1 @ X21)
% 0.20/0.48          | ~ (v1_funct_1 @ X22)
% 0.20/0.48          | ~ (v1_funct_2 @ X22 @ X19 @ X20)
% 0.20/0.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.48      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.20/0.48  thf('91', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.48          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.48          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | (r2_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.48             sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.48  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('93', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('94', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.20/0.48          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | (r2_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.48             sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.20/0.48  thf('95', plain,
% 0.20/0.48      (((r2_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['88', '94'])).
% 0.20/0.48  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('97', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('98', plain,
% 0.20/0.48      ((r2_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)),
% 0.20/0.48      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.48  thf('99', plain, ($false),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '87', '98'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
