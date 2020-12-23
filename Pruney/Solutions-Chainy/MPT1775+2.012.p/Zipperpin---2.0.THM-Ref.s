%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Re6mNkV96F

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 440 expanded)
%              Number of leaves         :   41 ( 139 expanded)
%              Depth                    :   30
%              Number of atoms          : 2045 (15547 expanded)
%              Number of equality atoms :   13 ( 197 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t86_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_tsep_1 @ C @ D )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ( m1_connsp_2 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( X21
       != ( u1_struct_0 @ X19 ) )
      | ~ ( v1_tsep_1 @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X19 ) @ X20 )
      | ~ ( v1_tsep_1 @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('34',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('41',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('49',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['41'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X30 )
      | ( X30 != X33 )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('52',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['48','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['47','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['45'])).

thf('71',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['41'])).

thf('83',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['46','81','82'])).

thf('84',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['44','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_tmap_1 @ X37 @ X34 @ ( k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40 ) @ X39 )
      | ( r1_tmap_1 @ X35 @ X34 @ X40 @ X41 )
      | ( X41 != X39 )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X41 )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('87',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X39 )
      | ( r1_tmap_1 @ X35 @ X34 @ X40 @ X39 )
      | ~ ( r1_tmap_1 @ X37 @ X34 @ ( k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_pre_topc @ X37 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('100',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D @ sk_F )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','102'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('104',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('106',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('107',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','109'])).

thf('111',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['45'])).

thf('112',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['46','81'])).

thf('113',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('115',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['119','120'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('122',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('123',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['116','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Re6mNkV96F
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 140 iterations in 0.073s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(t86_tmap_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                         ( v1_funct_2 @
% 0.21/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                         ( m1_subset_1 @
% 0.21/0.53                           E @ 
% 0.21/0.53                           ( k1_zfmisc_1 @
% 0.21/0.53                             ( k2_zfmisc_1 @
% 0.21/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.53                         ( ![F:$i]:
% 0.21/0.53                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                             ( ![G:$i]:
% 0.21/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                                 ( ( ( F ) = ( G ) ) =>
% 0.21/0.53                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.21/0.53                                     ( r1_tmap_1 @
% 0.21/0.53                                       C @ B @ 
% 0.21/0.53                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53                ( l1_pre_topc @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                            ( v1_funct_2 @
% 0.21/0.53                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                            ( m1_subset_1 @
% 0.21/0.53                              E @ 
% 0.21/0.53                              ( k1_zfmisc_1 @
% 0.21/0.53                                ( k2_zfmisc_1 @
% 0.21/0.53                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.53                            ( ![F:$i]:
% 0.21/0.53                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                                ( ![G:$i]:
% 0.21/0.53                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                                    ( ( ( F ) = ( G ) ) =>
% 0.21/0.53                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.21/0.53                                        ( r1_tmap_1 @
% 0.21/0.53                                          C @ B @ 
% 0.21/0.53                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(t2_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r2_hidden @ X2 @ X3)
% 0.21/0.53          | (v1_xboole_0 @ X3)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.53        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t1_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( m1_subset_1 @
% 0.21/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X22 @ X23)
% 0.21/0.53          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.21/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.53          | ~ (l1_pre_topc @ X23))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_D)
% 0.21/0.53        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.53          | (l1_pre_topc @ X13)
% 0.21/0.53          | ~ (l1_pre_topc @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.53  thf(t5_connsp_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.21/0.53                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.53          | ~ (v3_pre_topc @ X16 @ X17)
% 0.21/0.53          | ~ (r2_hidden @ X18 @ X16)
% 0.21/0.53          | (m1_connsp_2 @ X16 @ X17 @ X18)
% 0.21/0.53          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.21/0.53          | ~ (l1_pre_topc @ X17)
% 0.21/0.53          | ~ (v2_pre_topc @ X17)
% 0.21/0.53          | (v2_struct_0 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.53          | (v2_pre_topc @ X10)
% 0.21/0.53          | ~ (l1_pre_topc @ X11)
% 0.21/0.53          | ~ (v2_pre_topc @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.53  thf('24', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.53          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.53  thf(t16_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.53                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.53                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.53          | ((X21) != (u1_struct_0 @ X19))
% 0.21/0.53          | ~ (v1_tsep_1 @ X19 @ X20)
% 0.21/0.53          | ~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.53          | (v3_pre_topc @ X21 @ X20)
% 0.21/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.53          | ~ (l1_pre_topc @ X20)
% 0.21/0.53          | ~ (v2_pre_topc @ X20))),
% 0.21/0.53      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X20)
% 0.21/0.53          | ~ (l1_pre_topc @ X20)
% 0.21/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.21/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.53          | (v3_pre_topc @ (u1_struct_0 @ X19) @ X20)
% 0.21/0.53          | ~ (v1_tsep_1 @ X19 @ X20)
% 0.21/0.53          | ~ (m1_pre_topc @ X19 @ X20))),
% 0.21/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.53        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.53        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.21/0.53        | ~ (l1_pre_topc @ sk_D)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '28'])).
% 0.21/0.53  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('33', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.53  thf('34', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_D)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.53        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.21/0.53        | (v2_struct_0 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '35'])).
% 0.21/0.53  thf('37', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.21/0.53        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.21/0.53      inference('clc', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.53        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['41'])).
% 0.21/0.53  thf('43', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.21/0.53       ~
% 0.21/0.53       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.21/0.53      inference('split', [status(esa)], ['45'])).
% 0.21/0.53  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('48', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('split', [status(esa)], ['41'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t81_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                         ( v1_funct_2 @
% 0.21/0.53                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                         ( m1_subset_1 @
% 0.21/0.53                           E @ 
% 0.21/0.53                           ( k1_zfmisc_1 @
% 0.21/0.53                             ( k2_zfmisc_1 @
% 0.21/0.53                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                       ( ![F:$i]:
% 0.21/0.53                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                           ( ![G:$i]:
% 0.21/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                               ( ( ( ( F ) = ( G ) ) & 
% 0.21/0.53                                   ( m1_pre_topc @ D @ C ) & 
% 0.21/0.53                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.21/0.53                                 ( r1_tmap_1 @
% 0.21/0.53                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.53                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X27)
% 0.21/0.53          | ~ (v2_pre_topc @ X27)
% 0.21/0.53          | ~ (l1_pre_topc @ X27)
% 0.21/0.53          | (v2_struct_0 @ X28)
% 0.21/0.53          | ~ (m1_pre_topc @ X28 @ X29)
% 0.21/0.53          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.21/0.53          | ~ (m1_pre_topc @ X28 @ X31)
% 0.21/0.53          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X30)
% 0.21/0.53          | ((X30) != (X33))
% 0.21/0.53          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.21/0.53             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.21/0.53          | ~ (m1_subset_1 @ X32 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.21/0.53          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.21/0.53          | ~ (v1_funct_1 @ X32)
% 0.21/0.53          | ~ (m1_pre_topc @ X31 @ X29)
% 0.21/0.53          | (v2_struct_0 @ X31)
% 0.21/0.53          | ~ (l1_pre_topc @ X29)
% 0.21/0.53          | ~ (v2_pre_topc @ X29)
% 0.21/0.53          | (v2_struct_0 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X29)
% 0.21/0.53          | ~ (v2_pre_topc @ X29)
% 0.21/0.53          | ~ (l1_pre_topc @ X29)
% 0.21/0.53          | (v2_struct_0 @ X31)
% 0.21/0.53          | ~ (m1_pre_topc @ X31 @ X29)
% 0.21/0.53          | ~ (v1_funct_1 @ X32)
% 0.21/0.53          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.21/0.53          | ~ (m1_subset_1 @ X32 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.21/0.53          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.21/0.53             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.21/0.53          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X33)
% 0.21/0.53          | ~ (m1_pre_topc @ X28 @ X31)
% 0.21/0.53          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.21/0.53          | ~ (m1_pre_topc @ X28 @ X29)
% 0.21/0.53          | (v2_struct_0 @ X28)
% 0.21/0.53          | ~ (l1_pre_topc @ X27)
% 0.21/0.53          | ~ (v2_pre_topc @ X27)
% 0.21/0.53          | (v2_struct_0 @ X27))),
% 0.21/0.53      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.21/0.53             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | ~ (l1_pre_topc @ X1)
% 0.21/0.53          | ~ (v2_pre_topc @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '52'])).
% 0.21/0.53  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.53          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.21/0.53          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.21/0.53             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | ~ (l1_pre_topc @ X1)
% 0.21/0.53          | ~ (v2_pre_topc @ X1)
% 0.21/0.53          | (v2_struct_0 @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          ((v2_struct_0 @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.21/0.53           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53           | (v2_struct_0 @ X1)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['49', '58'])).
% 0.21/0.53  thf('60', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          ((v2_struct_0 @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.53           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.21/0.53           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.53           | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53           | (v2_struct_0 @ X1)
% 0.21/0.53           | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ sk_C)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.53           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ X0)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '61'])).
% 0.21/0.53  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((v2_struct_0 @ sk_B)
% 0.21/0.53           | (v2_struct_0 @ sk_C)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.53           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.53           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.53           | (v2_struct_0 @ sk_D)
% 0.21/0.53           | ~ (l1_pre_topc @ X0)
% 0.21/0.53           | ~ (v2_pre_topc @ X0)
% 0.21/0.53           | (v2_struct_0 @ X0)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A)
% 0.21/0.53         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53         | (v2_struct_0 @ sk_D)
% 0.21/0.53         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.21/0.53         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.53         | (v2_struct_0 @ sk_C)
% 0.21/0.53         | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '64'])).
% 0.21/0.53  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('68', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A)
% 0.21/0.53         | (v2_struct_0 @ sk_D)
% 0.21/0.53         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.53         | (v2_struct_0 @ sk_C)
% 0.21/0.53         | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.53      inference('split', [status(esa)], ['45'])).
% 0.21/0.53  thf('71', plain, (((sk_F) = (sk_G))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.53      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_C)
% 0.21/0.53         | (v2_struct_0 @ sk_D)
% 0.21/0.53         | (v2_struct_0 @ sk_A)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['69', '72'])).
% 0.21/0.53  thf('74', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.53  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('77', plain,
% 0.21/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('clc', [status(thm)], ['75', '76'])).
% 0.21/0.53  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_C))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.21/0.53             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.53  thf('80', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.21/0.53       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.21/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.21/0.53       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.21/0.53      inference('split', [status(esa)], ['41'])).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['46', '81', '82'])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.21/0.53        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['44', '83'])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_E @ 
% 0.21/0.53        (k1_zfmisc_1 @ 
% 0.21/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t83_tmap_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.53             ( l1_pre_topc @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.53                         ( v1_funct_2 @
% 0.21/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.53                         ( m1_subset_1 @
% 0.21/0.53                           E @ 
% 0.21/0.53                           ( k1_zfmisc_1 @
% 0.21/0.53                             ( k2_zfmisc_1 @
% 0.21/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.53                         ( ![F:$i]:
% 0.21/0.53                           ( ( m1_subset_1 @
% 0.21/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.21/0.53                             ( ![G:$i]:
% 0.21/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.53                                 ( ![H:$i]:
% 0.21/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.53                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.21/0.53                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.21/0.53                                         ( ( G ) = ( H ) ) ) =>
% 0.21/0.53                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.21/0.53                                         ( r1_tmap_1 @
% 0.21/0.53                                           C @ B @ 
% 0.21/0.53                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.21/0.53                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, 
% 0.21/0.53         X41 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X34)
% 0.21/0.53          | ~ (v2_pre_topc @ X34)
% 0.21/0.53          | ~ (l1_pre_topc @ X34)
% 0.21/0.53          | (v2_struct_0 @ X35)
% 0.21/0.53          | ~ (m1_pre_topc @ X35 @ X36)
% 0.21/0.53          | ~ (m1_pre_topc @ X37 @ X35)
% 0.21/0.53          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.21/0.53          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.21/0.53          | ~ (r1_tmap_1 @ X37 @ X34 @ 
% 0.21/0.53               (k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40) @ X39)
% 0.21/0.53          | (r1_tmap_1 @ X35 @ X34 @ X40 @ X41)
% 0.21/0.53          | ((X41) != (X39))
% 0.21/0.53          | ~ (m1_connsp_2 @ X38 @ X35 @ X41)
% 0.21/0.53          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X37))
% 0.21/0.53          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X35))
% 0.21/0.53          | ~ (m1_subset_1 @ X40 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))))
% 0.21/0.53          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))
% 0.21/0.53          | ~ (v1_funct_1 @ X40)
% 0.21/0.53          | ~ (m1_pre_topc @ X37 @ X36)
% 0.21/0.53          | (v2_struct_0 @ X37)
% 0.21/0.53          | ~ (l1_pre_topc @ X36)
% 0.21/0.53          | ~ (v2_pre_topc @ X36)
% 0.21/0.53          | (v2_struct_0 @ X36))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X36)
% 0.21/0.53          | ~ (v2_pre_topc @ X36)
% 0.21/0.53          | ~ (l1_pre_topc @ X36)
% 0.21/0.53          | (v2_struct_0 @ X37)
% 0.21/0.53          | ~ (m1_pre_topc @ X37 @ X36)
% 0.21/0.53          | ~ (v1_funct_1 @ X40)
% 0.21/0.53          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))
% 0.21/0.53          | ~ (m1_subset_1 @ X40 @ 
% 0.21/0.53               (k1_zfmisc_1 @ 
% 0.21/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))))
% 0.21/0.53          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X35))
% 0.21/0.53          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X37))
% 0.21/0.53          | ~ (m1_connsp_2 @ X38 @ X35 @ X39)
% 0.21/0.53          | (r1_tmap_1 @ X35 @ X34 @ X40 @ X39)
% 0.21/0.53          | ~ (r1_tmap_1 @ X37 @ X34 @ 
% 0.21/0.53               (k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40) @ X39)
% 0.21/0.53          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.21/0.53          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.21/0.53          | ~ (m1_pre_topc @ X37 @ X35)
% 0.21/0.53          | ~ (m1_pre_topc @ X35 @ X36)
% 0.21/0.53          | (v2_struct_0 @ X35)
% 0.21/0.53          | ~ (l1_pre_topc @ X34)
% 0.21/0.53          | ~ (v2_pre_topc @ X34)
% 0.21/0.53          | (v2_struct_0 @ X34))),
% 0.21/0.53      inference('simplify', [status(thm)], ['86'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.21/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53          | (v2_struct_0 @ X1)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['85', '87'])).
% 0.21/0.53  thf('89', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('93', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_B)
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.21/0.53               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.21/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.21/0.53          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.21/0.53          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.53          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.53          | (v2_struct_0 @ X1)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.21/0.53  thf('94', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_C)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.53          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.21/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.53          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.53          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.53          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['84', '93'])).
% 0.21/0.53  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('97', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('98', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('99', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('100', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('102', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_C)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.53          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.21/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.21/0.53          | (v2_struct_0 @ sk_D)
% 0.21/0.53          | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)],
% 0.21/0.53                ['94', '95', '96', '97', '98', '99', '100', '101'])).
% 0.21/0.53  thf('103', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.53        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.21/0.53        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '102'])).
% 0.21/0.53  thf(dt_k2_subset_1, axiom,
% 0.21/0.53    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.53  thf('104', plain,
% 0.21/0.53      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.53  thf('105', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.53  thf('106', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['104', '105'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('107', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('108', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.53  thf('109', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.53        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['103', '108'])).
% 0.21/0.53  thf('110', plain,
% 0.21/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '109'])).
% 0.21/0.53  thf('111', plain,
% 0.21/0.53      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.21/0.53         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.53      inference('split', [status(esa)], ['45'])).
% 0.21/0.53  thf('112', plain, (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['46', '81'])).
% 0.21/0.53  thf('113', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['111', '112'])).
% 0.21/0.53  thf('114', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['110', '113'])).
% 0.21/0.53  thf(fc2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('115', plain,
% 0.21/0.53      (![X15 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.53          | ~ (l1_struct_0 @ X15)
% 0.21/0.53          | (v2_struct_0 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('116', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['114', '115'])).
% 0.21/0.53  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('118', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.53          | (l1_pre_topc @ X13)
% 0.21/0.53          | ~ (l1_pre_topc @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('119', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.53  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('121', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.53      inference('demod', [status(thm)], ['119', '120'])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('122', plain,
% 0.21/0.53      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('123', plain, ((l1_struct_0 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['121', '122'])).
% 0.21/0.53  thf('124', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A)
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['116', '123'])).
% 0.21/0.53  thf('125', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_D)
% 0.21/0.53        | (v2_struct_0 @ sk_C)
% 0.21/0.53        | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['124'])).
% 0.21/0.53  thf('126', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('127', plain,
% 0.21/0.53      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.53  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('129', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.21/0.53      inference('clc', [status(thm)], ['127', '128'])).
% 0.21/0.53  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('131', plain, ((v2_struct_0 @ sk_C)),
% 0.21/0.53      inference('clc', [status(thm)], ['129', '130'])).
% 0.21/0.53  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
