%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Wr3HVpMYo

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 147 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  909 (3159 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
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

thf('5',plain,(
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
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k2_partfun1 @ X18 @ X19 @ X17 @ X20 )
        = ( k7_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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
    inference(demod,[status(thm)],['5','6','7','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('23',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k7_relat_1 @ X6 @ X7 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

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

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) )
      | ( m1_pre_topc @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','35','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
    = sk_D ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_funct_2 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Wr3HVpMYo
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 79 iterations in 0.064s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(t74_tmap_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.54             ( l1_pre_topc @ B ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.54                     ( v1_funct_2 @
% 0.20/0.54                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                     ( m1_subset_1 @
% 0.20/0.54                       D @ 
% 0.20/0.54                       ( k1_zfmisc_1 @
% 0.20/0.54                         ( k2_zfmisc_1 @
% 0.20/0.54                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54                   ( r2_funct_2 @
% 0.20/0.54                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.54                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54            ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.54                ( l1_pre_topc @ B ) ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.54                  ( ![D:$i]:
% 0.20/0.54                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.54                        ( v1_funct_2 @
% 0.20/0.54                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                        ( m1_subset_1 @
% 0.20/0.54                          D @ 
% 0.20/0.54                          ( k1_zfmisc_1 @
% 0.20/0.54                            ( k2_zfmisc_1 @
% 0.20/0.54                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54                      ( r2_funct_2 @
% 0.20/0.54                        ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.54                        ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t74_tmap_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.54          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d5_tmap_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.54             ( l1_pre_topc @ B ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.54                   ( ![E:$i]:
% 0.20/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.54                         ( v1_funct_2 @
% 0.20/0.54                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                         ( m1_subset_1 @
% 0.20/0.54                           E @ 
% 0.20/0.54                           ( k1_zfmisc_1 @
% 0.20/0.54                             ( k2_zfmisc_1 @
% 0.20/0.54                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.54                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.54                           ( k2_partfun1 @
% 0.20/0.54                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.54                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X25)
% 0.20/0.54          | ~ (v2_pre_topc @ X25)
% 0.20/0.54          | ~ (l1_pre_topc @ X25)
% 0.20/0.54          | ~ (m1_pre_topc @ X26 @ X27)
% 0.20/0.54          | ~ (m1_pre_topc @ X26 @ X28)
% 0.20/0.54          | ((k3_tmap_1 @ X27 @ X25 @ X28 @ X26 @ X29)
% 0.20/0.54              = (k2_partfun1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25) @ 
% 0.20/0.54                 X29 @ (u1_struct_0 @ X26)))
% 0.20/0.54          | ~ (m1_subset_1 @ X29 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))))
% 0.20/0.54          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X25))
% 0.20/0.54          | ~ (v1_funct_1 @ X29)
% 0.20/0.54          | ~ (m1_pre_topc @ X28 @ X27)
% 0.20/0.54          | ~ (l1_pre_topc @ X27)
% 0.20/0.54          | ~ (v2_pre_topc @ X27)
% 0.20/0.54          | (v2_struct_0 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X0)
% 0.20/0.54          | ~ (v2_pre_topc @ X0)
% 0.20/0.54          | ~ (l1_pre_topc @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.54          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.20/0.54              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.54                 sk_D @ (u1_struct_0 @ X1)))
% 0.20/0.54          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.54          | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k2_partfun1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.54          | ~ (v1_funct_1 @ X17)
% 0.20/0.54          | ((k2_partfun1 @ X18 @ X19 @ X17 @ X20) = (k7_relat_1 @ X17 @ X20)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.54            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.20/0.54          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.54           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('14', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X0)
% 0.20/0.54          | ~ (v2_pre_topc @ X0)
% 0.20/0.54          | ~ (l1_pre_topc @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.54          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.20/0.54              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X1)))
% 0.20/0.54          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.20/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.54          | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['5', '6', '7', '12', '13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.54          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.20/0.54              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['2', '15'])).
% 0.20/0.54  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.20/0.54          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.20/0.54              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D)
% 0.20/0.54            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.20/0.54        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         ((m1_subset_1 @ (k1_relset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 0.20/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((m1_subset_1 @ 
% 0.20/0.54        (k1_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (((k1_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.20/0.54         = (k1_relat_1 @ sk_D))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.54  thf(t3_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf(t97_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.54         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.20/0.54          | ((k7_relat_1 @ X6 @ X7) = (X6))
% 0.20/0.54          | ~ (v1_relat_1 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.54        | ((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( v1_relat_1 @ C ) ))).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         ((v1_relat_1 @ X8)
% 0.20/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.54  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.20/0.54      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.54  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf(t4_tsep_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.54               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.54                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X30 @ X31)
% 0.20/0.54          | ~ (r1_tarski @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32))
% 0.20/0.54          | (m1_pre_topc @ X30 @ X32)
% 0.20/0.54          | ~ (m1_pre_topc @ X32 @ X31)
% 0.20/0.54          | ~ (l1_pre_topc @ X31)
% 0.20/0.54          | ~ (v2_pre_topc @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (v2_pre_topc @ X1)
% 0.20/0.54          | ~ (l1_pre_topc @ X1)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.54          | (m1_pre_topc @ X0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((m1_pre_topc @ X0 @ X0)
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.54          | ~ (l1_pre_topc @ X1)
% 0.20/0.54          | ~ (v2_pre_topc @ X1))),
% 0.20/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (m1_pre_topc @ sk_C @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '41'])).
% 0.20/0.54  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.20/0.54        | (v2_struct_0 @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['20', '35', '45'])).
% 0.20/0.54  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B)
% 0.20/0.54        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D)))),
% 0.20/0.54      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.54  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('50', plain, (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))),
% 0.20/0.54      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(reflexivity_r2_funct_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.54         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         ((r2_funct_2 @ X21 @ X22 @ X23 @ X23)
% 0.20/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.54          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.20/0.54          | ~ (v1_funct_1 @ X23)
% 0.20/0.54          | ~ (v1_funct_1 @ X24)
% 0.20/0.54          | ~ (v1_funct_2 @ X24 @ X21 @ X22)
% 0.20/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.54      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.54             (k1_zfmisc_1 @ 
% 0.20/0.54              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.54          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.54          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.54             sk_D))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.54             (k1_zfmisc_1 @ 
% 0.20/0.54              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.20/0.54          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.20/0.54          | ~ (v1_funct_1 @ X0)
% 0.20/0.54          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.20/0.54             sk_D))),
% 0.20/0.54      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.54        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '57'])).
% 0.20/0.54  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)),
% 0.20/0.54      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.54  thf('62', plain, ($false),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '50', '61'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
