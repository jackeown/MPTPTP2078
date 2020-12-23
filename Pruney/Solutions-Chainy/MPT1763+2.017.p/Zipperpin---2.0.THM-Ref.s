%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r7posEv52p

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 140 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  801 (2731 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( m1_pre_topc @ X26 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( ( k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) @ X25 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k2_partfun1 @ X12 @ X13 @ X11 @ X14 )
        = ( k7_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','8','13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['26','31'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k7_relat_1 @ X6 @ X7 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('36',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
    = sk_D ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_funct_2 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_funct_2 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r7posEv52p
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:19:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 38 iterations in 0.023s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.45  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.45  thf(t74_tmap_1, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45             ( l1_pre_topc @ B ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.45               ( ![D:$i]:
% 0.20/0.45                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.45                     ( v1_funct_2 @
% 0.20/0.45                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.45                     ( m1_subset_1 @
% 0.20/0.45                       D @ 
% 0.20/0.45                       ( k1_zfmisc_1 @
% 0.20/0.45                         ( k2_zfmisc_1 @
% 0.20/0.45                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.45                   ( r2_funct_2 @
% 0.20/0.45                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.45                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.45            ( l1_pre_topc @ A ) ) =>
% 0.20/0.45          ( ![B:$i]:
% 0.20/0.45            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45                ( l1_pre_topc @ B ) ) =>
% 0.20/0.45              ( ![C:$i]:
% 0.20/0.45                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.45                  ( ![D:$i]:
% 0.20/0.45                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.45                        ( v1_funct_2 @
% 0.20/0.45                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.45                        ( m1_subset_1 @
% 0.20/0.45                          D @ 
% 0.20/0.45                          ( k1_zfmisc_1 @
% 0.20/0.45                            ( k2_zfmisc_1 @
% 0.20/0.45                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.45                      ( r2_funct_2 @
% 0.20/0.45                        ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.45                        ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t74_tmap_1])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.45          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t2_tsep_1, axiom,
% 0.20/0.45    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X26 : $i]: ((m1_pre_topc @ X26 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.20/0.45      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.45  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(d5_tmap_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45             ( l1_pre_topc @ B ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.45               ( ![D:$i]:
% 0.20/0.45                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.45                   ( ![E:$i]:
% 0.20/0.45                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.45                         ( v1_funct_2 @
% 0.20/0.45                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.45                         ( m1_subset_1 @
% 0.20/0.45                           E @ 
% 0.20/0.45                           ( k1_zfmisc_1 @
% 0.20/0.45                             ( k2_zfmisc_1 @
% 0.20/0.45                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.45                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.45                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.45                           ( k2_partfun1 @
% 0.20/0.45                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.45                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X21)
% 0.20/0.45          | ~ (v2_pre_topc @ X21)
% 0.20/0.45          | ~ (l1_pre_topc @ X21)
% 0.20/0.45          | ~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.45          | ~ (m1_pre_topc @ X22 @ X24)
% 0.20/0.45          | ((k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21) @ 
% 0.20/0.45                 X25 @ (u1_struct_0 @ X22)))
% 0.20/0.45          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.45               (k1_zfmisc_1 @ 
% 0.20/0.45                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))))
% 0.20/0.45          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))
% 0.20/0.45          | ~ (v1_funct_1 @ X25)
% 0.20/0.45          | ~ (m1_pre_topc @ X24 @ X23)
% 0.20/0.45          | ~ (l1_pre_topc @ X23)
% 0.20/0.45          | ~ (v2_pre_topc @ X23)
% 0.20/0.45          | (v2_struct_0 @ X23))),
% 0.20/0.45      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X0)
% 0.20/0.45          | ~ (v2_pre_topc @ X0)
% 0.20/0.45          | ~ (l1_pre_topc @ X0)
% 0.20/0.45          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.45          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.45          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 sk_D @ (u1_struct_0 @ X1)))
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.45          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.45          | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.45  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(redefinition_k2_partfun1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.20/0.45          | ~ (v1_funct_1 @ X11)
% 0.20/0.45          | ((k2_partfun1 @ X12 @ X13 @ X11 @ X14) = (k7_relat_1 @ X11 @ X14)))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.45            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.20/0.45          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.45           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X0)
% 0.20/0.45          | ~ (v2_pre_topc @ X0)
% 0.20/0.45          | ~ (l1_pre_topc @ X0)
% 0.20/0.45          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.45          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.20/0.45              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X1)))
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.45          | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('demod', [status(thm)], ['6', '7', '8', '13', '14', '15'])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_B)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.45          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.20/0.45              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.20/0.45          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.45          | (v2_struct_0 @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '16'])).
% 0.20/0.45  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_B)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.45          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.20/0.45              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.20/0.45          | (v2_struct_0 @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_A)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D)
% 0.20/0.45            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.20/0.45        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.45        | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '20'])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(cc2_relset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.45         ((v4_relat_1 @ X8 @ X9)
% 0.20/0.45          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.45  thf('24', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.45  thf(d18_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.45  thf('25', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i]:
% 0.20/0.45         (~ (v4_relat_1 @ X2 @ X3)
% 0.20/0.45          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.20/0.45          | ~ (v1_relat_1 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.45        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(cc2_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.45          | (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ 
% 0.20/0.45           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))
% 0.20/0.45        | (v1_relat_1 @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.45  thf(fc6_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.45  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.45      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.45  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.20/0.45      inference('demod', [status(thm)], ['26', '31'])).
% 0.20/0.45  thf(t97_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.45         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i]:
% 0.20/0.45         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.20/0.45          | ((k7_relat_1 @ X6 @ X7) = (X6))
% 0.20/0.45          | ~ (v1_relat_1 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.45  thf('34', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.45        | ((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.45  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.45      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.45  thf('36', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.20/0.45      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.45  thf('37', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_A)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.45        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.45        | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('demod', [status(thm)], ['21', '36'])).
% 0.20/0.45  thf('38', plain,
% 0.20/0.45      ((~ (l1_pre_topc @ sk_C)
% 0.20/0.45        | (v2_struct_0 @ sk_B)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.45        | (v2_struct_0 @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '37'])).
% 0.20/0.45  thf('39', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(dt_m1_pre_topc, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( l1_pre_topc @ A ) =>
% 0.20/0.45       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.45  thf('40', plain,
% 0.20/0.45      (![X19 : $i, X20 : $i]:
% 0.20/0.45         (~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.45          | (l1_pre_topc @ X19)
% 0.20/0.45          | ~ (l1_pre_topc @ X20))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.45  thf('41', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.45  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('43', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.45      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.45  thf('44', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_B)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.45        | (v2_struct_0 @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['38', '43'])).
% 0.20/0.45  thf('45', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('46', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_A)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D)))),
% 0.20/0.45      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.45  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('48', plain, (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))),
% 0.20/0.45      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.45  thf('49', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(redefinition_r2_funct_2, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.45         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.45       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.45  thf('50', plain,
% 0.20/0.45      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.20/0.45          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.20/0.45          | ~ (v1_funct_1 @ X15)
% 0.20/0.45          | ~ (v1_funct_1 @ X18)
% 0.20/0.45          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.20/0.45          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.20/0.45          | (r2_funct_2 @ X16 @ X17 @ X15 @ X18)
% 0.20/0.45          | ((X15) != (X18)))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.20/0.45  thf('51', plain,
% 0.20/0.45      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.45         ((r2_funct_2 @ X16 @ X17 @ X18 @ X18)
% 0.20/0.45          | ~ (v1_funct_1 @ X18)
% 0.20/0.45          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.20/0.45          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.45      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.45  thf('52', plain,
% 0.20/0.45      ((~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.45        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.45        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.45           sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['49', '51'])).
% 0.20/0.45  thf('53', plain,
% 0.20/0.45      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('55', plain,
% 0.20/0.45      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)),
% 0.20/0.45      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.45  thf('56', plain, ($false),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '48', '55'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
