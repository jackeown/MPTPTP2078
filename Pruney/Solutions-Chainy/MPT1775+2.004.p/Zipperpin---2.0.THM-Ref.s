%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CpAS0X28wv

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 434 expanded)
%              Number of leaves         :   38 ( 136 expanded)
%              Depth                    :   30
%              Number of atoms          : 2024 (15526 expanded)
%              Number of equality atoms :   13 ( 197 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

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
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( m1_connsp_2 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X26 @ X29 )
      | ~ ( r1_tmap_1 @ X29 @ X25 @ X30 @ X28 )
      | ( X28 != X31 )
      | ( r1_tmap_1 @ X26 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X26 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30 ) @ X31 )
      | ~ ( r1_tmap_1 @ X29 @ X25 @ X30 @ X31 )
      | ~ ( m1_pre_topc @ X26 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X39 )
      | ( X39 != X37 )
      | ~ ( m1_connsp_2 @ X36 @ X33 @ X39 )
      | ~ ( r1_tarski @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('87',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r1_tarski @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_connsp_2 @ X36 @ X33 @ X37 )
      | ( r1_tmap_1 @ X33 @ X32 @ X38 @ X37 )
      | ~ ( r1_tmap_1 @ X35 @ X32 @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','106'])).

thf('108',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['45'])).

thf('109',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['46','81'])).

thf('110',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('112',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['116','117'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('119',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('120',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['113','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CpAS0X28wv
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 110 iterations in 0.060s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(t86_tmap_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.55                         ( ![F:$i]:
% 0.20/0.55                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                             ( ![G:$i]:
% 0.20/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.55                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.20/0.55                                     ( r1_tmap_1 @
% 0.20/0.55                                       C @ B @ 
% 0.20/0.55                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55                ( l1_pre_topc @ B ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.55                  ( ![D:$i]:
% 0.20/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.55                      ( ![E:$i]:
% 0.20/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                            ( v1_funct_2 @
% 0.20/0.55                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                            ( m1_subset_1 @
% 0.20/0.55                              E @ 
% 0.20/0.55                              ( k1_zfmisc_1 @
% 0.20/0.55                                ( k2_zfmisc_1 @
% 0.20/0.55                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.55                            ( ![F:$i]:
% 0.20/0.55                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.55                                ( ![G:$i]:
% 0.20/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                    ( ( ( F ) = ( G ) ) =>
% 0.20/0.55                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.20/0.55                                        ( r1_tmap_1 @
% 0.20/0.55                                          C @ B @ 
% 0.20/0.55                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.20/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('2', plain, (((sk_F) = (sk_G))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf(t2_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         ((r2_hidden @ X3 @ X4)
% 0.20/0.55          | (v1_xboole_0 @ X4)
% 0.20/0.55          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf('6', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t1_tsep_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( m1_subset_1 @
% 0.20/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.55          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55          | ~ (l1_pre_topc @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_m1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.55          | (l1_pre_topc @ X11)
% 0.20/0.55          | ~ (l1_pre_topc @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.55  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.55  thf(t5_connsp_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.55                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.55          | ~ (v3_pre_topc @ X14 @ X15)
% 0.20/0.55          | ~ (r2_hidden @ X16 @ X14)
% 0.20/0.55          | (m1_connsp_2 @ X14 @ X15 @ X16)
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.55          | ~ (l1_pre_topc @ X15)
% 0.20/0.55          | ~ (v2_pre_topc @ X15)
% 0.20/0.55          | (v2_struct_0 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ X0)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.55          | (v2_pre_topc @ X8)
% 0.20/0.55          | ~ (l1_pre_topc @ X9)
% 0.20/0.55          | ~ (v2_pre_topc @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('23', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.55  thf('24', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ X0)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D))),
% 0.20/0.55      inference('demod', [status(thm)], ['17', '23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.55  thf(t16_tsep_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.55                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.55          | ((X19) != (u1_struct_0 @ X17))
% 0.20/0.55          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.20/0.55          | ~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.55          | (v3_pre_topc @ X19 @ X18)
% 0.20/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | ~ (l1_pre_topc @ X18)
% 0.20/0.55          | ~ (v2_pre_topc @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i]:
% 0.20/0.55         (~ (v2_pre_topc @ X18)
% 0.20/0.55          | ~ (l1_pre_topc @ X18)
% 0.20/0.55          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.20/0.55          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.20/0.55          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.20/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.55        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.55        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_D)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.55  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('33', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.55  thf('34', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_D)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.55          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ X0)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['25', '34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.55        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.20/0.55        | (v2_struct_0 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '35'])).
% 0.20/0.55  thf('37', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.20/0.55        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.56      inference('split', [status(esa)], ['41'])).
% 0.20/0.56  thf('43', plain, (((sk_F) = (sk_G))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.56        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.20/0.56       ~
% 0.20/0.56       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.56      inference('split', [status(esa)], ['45'])).
% 0.20/0.56  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('48', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('split', [status(esa)], ['41'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_E @ 
% 0.20/0.56        (k1_zfmisc_1 @ 
% 0.20/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t81_tmap_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.56             ( l1_pre_topc @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.56               ( ![D:$i]:
% 0.20/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.56                   ( ![E:$i]:
% 0.20/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.56                         ( v1_funct_2 @
% 0.20/0.56                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.56                         ( m1_subset_1 @
% 0.20/0.56                           E @ 
% 0.20/0.56                           ( k1_zfmisc_1 @
% 0.20/0.56                             ( k2_zfmisc_1 @
% 0.20/0.56                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.56                       ( ![F:$i]:
% 0.20/0.56                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.56                           ( ![G:$i]:
% 0.20/0.56                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.56                               ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.56                                   ( m1_pre_topc @ D @ C ) & 
% 0.20/0.56                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.20/0.56                                 ( r1_tmap_1 @
% 0.20/0.56                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.56                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X25)
% 0.20/0.56          | ~ (v2_pre_topc @ X25)
% 0.20/0.56          | ~ (l1_pre_topc @ X25)
% 0.20/0.56          | (v2_struct_0 @ X26)
% 0.20/0.56          | ~ (m1_pre_topc @ X26 @ X27)
% 0.20/0.56          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.20/0.56          | ~ (m1_pre_topc @ X26 @ X29)
% 0.20/0.56          | ~ (r1_tmap_1 @ X29 @ X25 @ X30 @ X28)
% 0.20/0.56          | ((X28) != (X31))
% 0.20/0.56          | (r1_tmap_1 @ X26 @ X25 @ 
% 0.20/0.56             (k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30) @ X31)
% 0.20/0.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X26))
% 0.20/0.56          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))))
% 0.20/0.56          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))
% 0.20/0.56          | ~ (v1_funct_1 @ X30)
% 0.20/0.56          | ~ (m1_pre_topc @ X29 @ X27)
% 0.20/0.56          | (v2_struct_0 @ X29)
% 0.20/0.56          | ~ (l1_pre_topc @ X27)
% 0.20/0.56          | ~ (v2_pre_topc @ X27)
% 0.20/0.56          | (v2_struct_0 @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X27)
% 0.20/0.56          | ~ (v2_pre_topc @ X27)
% 0.20/0.56          | ~ (l1_pre_topc @ X27)
% 0.20/0.56          | (v2_struct_0 @ X29)
% 0.20/0.56          | ~ (m1_pre_topc @ X29 @ X27)
% 0.20/0.56          | ~ (v1_funct_1 @ X30)
% 0.20/0.56          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))
% 0.20/0.56          | ~ (m1_subset_1 @ X30 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X25))))
% 0.20/0.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X26))
% 0.20/0.56          | (r1_tmap_1 @ X26 @ X25 @ 
% 0.20/0.56             (k3_tmap_1 @ X27 @ X25 @ X29 @ X26 @ X30) @ X31)
% 0.20/0.56          | ~ (r1_tmap_1 @ X29 @ X25 @ X30 @ X31)
% 0.20/0.56          | ~ (m1_pre_topc @ X26 @ X29)
% 0.20/0.56          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.20/0.56          | ~ (m1_pre_topc @ X26 @ X27)
% 0.20/0.56          | (v2_struct_0 @ X26)
% 0.20/0.56          | ~ (l1_pre_topc @ X25)
% 0.20/0.56          | ~ (v2_pre_topc @ X25)
% 0.20/0.56          | (v2_struct_0 @ X25))),
% 0.20/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.20/0.56          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.56             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.56          | (v2_struct_0 @ sk_D)
% 0.20/0.56          | ~ (l1_pre_topc @ X1)
% 0.20/0.56          | ~ (v2_pre_topc @ X1)
% 0.20/0.56          | (v2_struct_0 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['50', '52'])).
% 0.20/0.56  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.56          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.20/0.56          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.20/0.56             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.56          | (v2_struct_0 @ sk_D)
% 0.20/0.56          | ~ (l1_pre_topc @ X1)
% 0.20/0.56          | ~ (v2_pre_topc @ X1)
% 0.20/0.56          | (v2_struct_0 @ X1))),
% 0.20/0.56      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      ((![X0 : $i, X1 : $i]:
% 0.20/0.56          ((v2_struct_0 @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | (v2_struct_0 @ sk_D)
% 0.20/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.56           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.56           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.56           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.56           | (v2_struct_0 @ X1)
% 0.20/0.56           | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['49', '58'])).
% 0.20/0.56  thf('60', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      ((![X0 : $i, X1 : $i]:
% 0.20/0.56          ((v2_struct_0 @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | (v2_struct_0 @ sk_D)
% 0.20/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.56           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.56           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.56           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.56           | (v2_struct_0 @ X1)
% 0.20/0.56           | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_B)
% 0.20/0.56           | (v2_struct_0 @ sk_C)
% 0.20/0.56           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.56           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.56           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.56           | (v2_struct_0 @ sk_D)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)
% 0.20/0.56           | (v2_struct_0 @ X0)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['48', '61'])).
% 0.20/0.56  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_B)
% 0.20/0.56           | (v2_struct_0 @ sk_C)
% 0.20/0.56           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.56           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.56           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.56           | (v2_struct_0 @ sk_D)
% 0.20/0.56           | ~ (l1_pre_topc @ X0)
% 0.20/0.56           | ~ (v2_pre_topc @ X0)
% 0.20/0.56           | (v2_struct_0 @ X0)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A)
% 0.20/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_D)
% 0.20/0.56         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.56         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.56         | (v2_struct_0 @ sk_C)
% 0.20/0.56         | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['47', '64'])).
% 0.20/0.56  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('68', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_D)
% 0.20/0.56         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.56         | (v2_struct_0 @ sk_C)
% 0.20/0.56         | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.20/0.56  thf('70', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.56      inference('split', [status(esa)], ['45'])).
% 0.20/0.56  thf('71', plain, (((sk_F) = (sk_G))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_B)
% 0.20/0.56         | (v2_struct_0 @ sk_C)
% 0.20/0.56         | (v2_struct_0 @ sk_D)
% 0.20/0.56         | (v2_struct_0 @ sk_A)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['69', '72'])).
% 0.20/0.56  thf('74', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.56  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('79', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_C))
% 0.20/0.56         <= (~
% 0.20/0.56             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.56             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('clc', [status(thm)], ['77', '78'])).
% 0.20/0.56  thf('80', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.20/0.56       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.20/0.56      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.56  thf('82', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.20/0.56       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.20/0.56      inference('split', [status(esa)], ['41'])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['46', '81', '82'])).
% 0.20/0.56  thf('84', plain,
% 0.20/0.56      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.20/0.56        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['44', '83'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_E @ 
% 0.20/0.56        (k1_zfmisc_1 @ 
% 0.20/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t83_tmap_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.56             ( l1_pre_topc @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.56               ( ![D:$i]:
% 0.20/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.56                   ( ![E:$i]:
% 0.20/0.56                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.56                         ( v1_funct_2 @
% 0.20/0.56                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.56                         ( m1_subset_1 @
% 0.20/0.56                           E @ 
% 0.20/0.56                           ( k1_zfmisc_1 @
% 0.20/0.56                             ( k2_zfmisc_1 @
% 0.20/0.56                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.56                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.56                         ( ![F:$i]:
% 0.20/0.56                           ( ( m1_subset_1 @
% 0.20/0.56                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.56                             ( ![G:$i]:
% 0.20/0.56                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.56                                 ( ![H:$i]:
% 0.20/0.56                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.56                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.56                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.20/0.56                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.56                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.20/0.56                                         ( r1_tmap_1 @
% 0.20/0.56                                           C @ B @ 
% 0.20/0.56                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.20/0.56                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('86', plain,
% 0.20/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.20/0.56         X39 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X32)
% 0.20/0.56          | ~ (v2_pre_topc @ X32)
% 0.20/0.56          | ~ (l1_pre_topc @ X32)
% 0.20/0.56          | (v2_struct_0 @ X33)
% 0.20/0.56          | ~ (m1_pre_topc @ X33 @ X34)
% 0.20/0.56          | ~ (m1_pre_topc @ X35 @ X33)
% 0.20/0.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.20/0.56          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.20/0.56          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 0.20/0.56               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 0.20/0.56          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X39)
% 0.20/0.56          | ((X39) != (X37))
% 0.20/0.56          | ~ (m1_connsp_2 @ X36 @ X33 @ X39)
% 0.20/0.56          | ~ (r1_tarski @ X36 @ (u1_struct_0 @ X35))
% 0.20/0.56          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X33))
% 0.20/0.56          | ~ (m1_subset_1 @ X38 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 0.20/0.56          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 0.20/0.56          | ~ (v1_funct_1 @ X38)
% 0.20/0.56          | ~ (m1_pre_topc @ X35 @ X34)
% 0.20/0.56          | (v2_struct_0 @ X35)
% 0.20/0.56          | ~ (l1_pre_topc @ X34)
% 0.20/0.56          | ~ (v2_pre_topc @ X34)
% 0.20/0.56          | (v2_struct_0 @ X34))),
% 0.20/0.56      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.20/0.56  thf('87', plain,
% 0.20/0.56      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.56         ((v2_struct_0 @ X34)
% 0.20/0.56          | ~ (v2_pre_topc @ X34)
% 0.20/0.56          | ~ (l1_pre_topc @ X34)
% 0.20/0.56          | (v2_struct_0 @ X35)
% 0.20/0.56          | ~ (m1_pre_topc @ X35 @ X34)
% 0.20/0.56          | ~ (v1_funct_1 @ X38)
% 0.20/0.56          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))
% 0.20/0.56          | ~ (m1_subset_1 @ X38 @ 
% 0.20/0.56               (k1_zfmisc_1 @ 
% 0.20/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32))))
% 0.20/0.56          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X33))
% 0.20/0.56          | ~ (r1_tarski @ X36 @ (u1_struct_0 @ X35))
% 0.20/0.56          | ~ (m1_connsp_2 @ X36 @ X33 @ X37)
% 0.20/0.56          | (r1_tmap_1 @ X33 @ X32 @ X38 @ X37)
% 0.20/0.56          | ~ (r1_tmap_1 @ X35 @ X32 @ 
% 0.20/0.56               (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ X38) @ X37)
% 0.20/0.56          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.20/0.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.20/0.56          | ~ (m1_pre_topc @ X35 @ X33)
% 0.20/0.56          | ~ (m1_pre_topc @ X33 @ X34)
% 0.20/0.56          | (v2_struct_0 @ X33)
% 0.20/0.56          | ~ (l1_pre_topc @ X32)
% 0.20/0.56          | ~ (v2_pre_topc @ X32)
% 0.20/0.56          | (v2_struct_0 @ X32))),
% 0.20/0.56      inference('simplify', [status(thm)], ['86'])).
% 0.20/0.56  thf('88', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ sk_D)
% 0.20/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.56          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.56          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.56          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.56          | (v2_struct_0 @ X1)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | (v2_struct_0 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['85', '87'])).
% 0.20/0.56  thf('89', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('93', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_B)
% 0.20/0.56          | (v2_struct_0 @ sk_D)
% 0.20/0.56          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.56          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.56          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.20/0.56               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.20/0.56          | ~ (m1_connsp_2 @ X2 @ sk_D @ X3)
% 0.20/0.56          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.56          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.56          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.56          | (v2_struct_0 @ X1)
% 0.20/0.56          | ~ (l1_pre_topc @ X0)
% 0.20/0.56          | ~ (v2_pre_topc @ X0)
% 0.20/0.56          | (v2_struct_0 @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.20/0.56  thf('94', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_C)
% 0.20/0.56          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.56          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.20/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.56          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.56          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.56          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_D)
% 0.20/0.56          | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['84', '93'])).
% 0.20/0.56  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('97', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('98', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('99', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('100', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('102', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_C)
% 0.20/0.56          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.56          | ~ (m1_connsp_2 @ X0 @ sk_D @ sk_F)
% 0.20/0.56          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.56          | (v2_struct_0 @ sk_D)
% 0.20/0.56          | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)],
% 0.20/0.56                ['94', '95', '96', '97', '98', '99', '100', '101'])).
% 0.20/0.56  thf('103', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_D)
% 0.20/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.56        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.20/0.56        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '102'])).
% 0.20/0.56  thf(d10_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('104', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.56  thf('105', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.56      inference('simplify', [status(thm)], ['104'])).
% 0.20/0.56  thf('106', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_D)
% 0.20/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.56        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D @ sk_F)
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['103', '105'])).
% 0.20/0.56  thf('107', plain,
% 0.20/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.56        | (v2_struct_0 @ sk_A)
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.20/0.56        | (v2_struct_0 @ sk_D)
% 0.20/0.56        | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '106'])).
% 0.20/0.56  thf('108', plain,
% 0.20/0.56      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.20/0.56         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.20/0.56      inference('split', [status(esa)], ['45'])).
% 0.20/0.56  thf('109', plain, (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['46', '81'])).
% 0.20/0.56  thf('110', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['108', '109'])).
% 0.20/0.56  thf('111', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_D)
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | (v2_struct_0 @ sk_A)
% 0.20/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['107', '110'])).
% 0.20/0.56  thf(fc2_struct_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.56  thf('112', plain,
% 0.20/0.56      (![X13 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.20/0.56          | ~ (l1_struct_0 @ X13)
% 0.20/0.56          | (v2_struct_0 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.56  thf('113', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | (v2_struct_0 @ sk_D)
% 0.20/0.56        | (v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.56  thf('114', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('115', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.56          | (l1_pre_topc @ X11)
% 0.20/0.56          | ~ (l1_pre_topc @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.56  thf('116', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.56  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('118', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.56      inference('demod', [status(thm)], ['116', '117'])).
% 0.20/0.56  thf(dt_l1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.56  thf('119', plain,
% 0.20/0.56      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.56  thf('120', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['118', '119'])).
% 0.20/0.56  thf('121', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | (v2_struct_0 @ sk_D)
% 0.20/0.56        | (v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['113', '120'])).
% 0.20/0.56  thf('122', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_B)
% 0.20/0.56        | (v2_struct_0 @ sk_D)
% 0.20/0.56        | (v2_struct_0 @ sk_C)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('simplify', [status(thm)], ['121'])).
% 0.20/0.56  thf('123', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('124', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.56  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('126', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.20/0.56      inference('clc', [status(thm)], ['124', '125'])).
% 0.20/0.56  thf('127', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('128', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.56      inference('clc', [status(thm)], ['126', '127'])).
% 0.20/0.56  thf('129', plain, ($false), inference('demod', [status(thm)], ['0', '128'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
