%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jgrpTMr5NJ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 127 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  781 (2671 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( ( k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) @ X23 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k2_partfun1 @ X12 @ X13 @ X11 @ X14 )
        = ( k7_relat_1 @ X11 @ X14 ) ) ) ),
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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3
        = ( k7_relat_1 @ X3 @ X4 ) )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

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

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ X24 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','29','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
      = sk_D ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D )
    = sk_D ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
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

thf('46',plain,(
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

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_funct_2 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jgrpTMr5NJ
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 38 iterations in 0.022s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.19/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(t74_tmap_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48             ( l1_pre_topc @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.48                     ( v1_funct_2 @
% 0.19/0.48                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48                     ( m1_subset_1 @
% 0.19/0.48                       D @ 
% 0.19/0.48                       ( k1_zfmisc_1 @
% 0.19/0.48                         ( k2_zfmisc_1 @
% 0.19/0.48                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.48                   ( r2_funct_2 @
% 0.19/0.48                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.19/0.48                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.48            ( l1_pre_topc @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48                ( l1_pre_topc @ B ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.48                  ( ![D:$i]:
% 0.19/0.48                    ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.48                        ( v1_funct_2 @
% 0.19/0.48                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48                        ( m1_subset_1 @
% 0.19/0.48                          D @ 
% 0.19/0.48                          ( k1_zfmisc_1 @
% 0.19/0.48                            ( k2_zfmisc_1 @
% 0.19/0.48                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.48                      ( r2_funct_2 @
% 0.19/0.48                        ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.19/0.48                        ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t74_tmap_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.48          (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d5_tmap_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48             ( l1_pre_topc @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.48                   ( ![E:$i]:
% 0.19/0.48                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.48                         ( v1_funct_2 @
% 0.19/0.48                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48                         ( m1_subset_1 @
% 0.19/0.48                           E @ 
% 0.19/0.48                           ( k1_zfmisc_1 @
% 0.19/0.48                             ( k2_zfmisc_1 @
% 0.19/0.48                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.48                       ( ( m1_pre_topc @ D @ C ) =>
% 0.19/0.48                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.48                           ( k2_partfun1 @
% 0.19/0.48                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.19/0.48                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X19)
% 0.19/0.48          | ~ (v2_pre_topc @ X19)
% 0.19/0.48          | ~ (l1_pre_topc @ X19)
% 0.19/0.48          | ~ (m1_pre_topc @ X20 @ X21)
% 0.19/0.48          | ~ (m1_pre_topc @ X20 @ X22)
% 0.19/0.48          | ((k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23)
% 0.19/0.48              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19) @ 
% 0.19/0.48                 X23 @ (u1_struct_0 @ X20)))
% 0.19/0.48          | ~ (m1_subset_1 @ X23 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))))
% 0.19/0.48          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))
% 0.19/0.48          | ~ (v1_funct_1 @ X23)
% 0.19/0.48          | ~ (m1_pre_topc @ X22 @ X21)
% 0.19/0.48          | ~ (l1_pre_topc @ X21)
% 0.19/0.48          | ~ (v2_pre_topc @ X21)
% 0.19/0.48          | (v2_struct_0 @ X21))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X0)
% 0.19/0.48          | ~ (v2_pre_topc @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ X0)
% 0.19/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.19/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.19/0.48              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.48                 sk_D @ (u1_struct_0 @ X1)))
% 0.19/0.48          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.19/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k2_partfun1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.19/0.48          | ~ (v1_funct_1 @ X11)
% 0.19/0.48          | ((k2_partfun1 @ X12 @ X13 @ X11 @ X14) = (k7_relat_1 @ X11 @ X14)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.48            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.19/0.48          | ~ (v1_funct_1 @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.48           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('14', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X0)
% 0.19/0.48          | ~ (v2_pre_topc @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ X0)
% 0.19/0.48          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_D)
% 0.19/0.48              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X1)))
% 0.19/0.48          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.19/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.48          | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['5', '6', '7', '12', '13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_B)
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.19/0.48          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.19/0.48              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.48          | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '15'])).
% 0.19/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((v2_struct_0 @ sk_B)
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.19/0.48          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_D)
% 0.19/0.48              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.19/0.48          | (v2_struct_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D)
% 0.19/0.48            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.19/0.48        | ~ (m1_pre_topc @ sk_C @ sk_C)
% 0.19/0.48        | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc2_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         ((v4_relat_1 @ X8 @ X9)
% 0.19/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.48  thf('23', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf(t209_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]:
% 0.19/0.48         (((X3) = (k7_relat_1 @ X3 @ X4))
% 0.19/0.48          | ~ (v4_relat_1 @ X3 @ X4)
% 0.19/0.48          | ~ (v1_relat_1 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_D)
% 0.19/0.48        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc1_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( v1_relat_1 @ C ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.48         ((v1_relat_1 @ X5)
% 0.19/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.48  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '28'])).
% 0.19/0.48  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d10_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.48  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.48  thf(t4_tsep_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.48               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.19/0.48                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.48         (~ (m1_pre_topc @ X24 @ X25)
% 0.19/0.48          | ~ (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.19/0.48          | (m1_pre_topc @ X24 @ X26)
% 0.19/0.48          | ~ (m1_pre_topc @ X26 @ X25)
% 0.19/0.48          | ~ (l1_pre_topc @ X25)
% 0.19/0.48          | ~ (v2_pre_topc @ X25))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v2_pre_topc @ X1)
% 0.19/0.48          | ~ (l1_pre_topc @ X1)
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.48          | (m1_pre_topc @ X0 @ X0)
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((m1_pre_topc @ X0 @ X0)
% 0.19/0.48          | ~ (m1_pre_topc @ X0 @ X1)
% 0.19/0.48          | ~ (l1_pre_topc @ X1)
% 0.19/0.48          | ~ (v2_pre_topc @ X1))),
% 0.19/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.48        | (m1_pre_topc @ sk_C @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['30', '35'])).
% 0.19/0.48  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('39', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_A)
% 0.19/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))
% 0.19/0.48        | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '29', '39'])).
% 0.19/0.48  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      (((v2_struct_0 @ sk_B)
% 0.19/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D)))),
% 0.19/0.48      inference('clc', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('44', plain, (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_C @ sk_D) = (sk_D))),
% 0.19/0.48      inference('clc', [status(thm)], ['42', '43'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_D @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_r2_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.19/0.48          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.19/0.48          | ~ (v1_funct_1 @ X15)
% 0.19/0.48          | ~ (v1_funct_1 @ X18)
% 0.19/0.48          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.19/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.19/0.48          | (r2_funct_2 @ X16 @ X17 @ X15 @ X18)
% 0.19/0.48          | ((X15) != (X18)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.48         ((r2_funct_2 @ X16 @ X17 @ X18 @ X18)
% 0.19/0.48          | ~ (v1_funct_1 @ X18)
% 0.19/0.48          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.19/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      ((~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.19/0.48        | ~ (v1_funct_1 @ sk_D)
% 0.19/0.48        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.19/0.48           sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['45', '47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)),
% 0.19/0.48      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.19/0.48  thf('52', plain, ($false),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '44', '51'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
