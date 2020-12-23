%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btWUu60xSm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:21 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 455 expanded)
%              Number of leaves         :   38 ( 142 expanded)
%              Depth                    :   30
%              Number of atoms          : 2081 (16076 expanded)
%              Number of equality atoms :   13 ( 205 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_D_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
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
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v3_pre_topc @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D_1 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('21',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D_1 )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_tsep_1 @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('34',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D_1 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['18','24','25','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','35'])).

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

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['36','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf('44',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('45',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('53',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['45'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X27 @ X30 )
      | ~ ( r1_tmap_1 @ X30 @ X26 @ X31 @ X29 )
      | ( X29 != X32 )
      | ( r1_tmap_1 @ X27 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X30 @ X27 @ X31 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('56',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X27 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X30 @ X27 @ X31 ) @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X26 @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X27 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['49'])).

thf('75',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['45'])).

thf('87',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['50','85','86'])).

thf('88',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['48','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('90',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tmap_1 @ X36 @ X33 @ ( k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39 ) @ X38 )
      | ( r1_tmap_1 @ X34 @ X33 @ X39 @ X40 )
      | ( X40 != X38 )
      | ~ ( m1_connsp_2 @ X37 @ X34 @ X40 )
      | ~ ( r1_tarski @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('91',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r1_tarski @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_connsp_2 @ X37 @ X34 @ X38 )
      | ( r1_tmap_1 @ X34 @ X33 @ X39 @ X38 )
      | ~ ( r1_tmap_1 @ X36 @ X33 @ ( k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_F )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('104',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_F )
      | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','103','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','106'])).

thf('108',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','109'])).

thf('111',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['49'])).

thf('112',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['50','85'])).

thf('113',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
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
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('123',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['116','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btWUu60xSm
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 169 iterations in 0.071s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.36/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(t86_tmap_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.54                         ( v1_funct_2 @
% 0.36/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                         ( m1_subset_1 @
% 0.36/0.54                           E @ 
% 0.36/0.54                           ( k1_zfmisc_1 @
% 0.36/0.54                             ( k2_zfmisc_1 @
% 0.36/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.36/0.54                         ( ![F:$i]:
% 0.36/0.54                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                             ( ![G:$i]:
% 0.36/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.54                                 ( ( ( F ) = ( G ) ) =>
% 0.36/0.54                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.36/0.54                                     ( r1_tmap_1 @
% 0.36/0.54                                       C @ B @ 
% 0.36/0.54                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.54            ( l1_pre_topc @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54                ( l1_pre_topc @ B ) ) =>
% 0.36/0.54              ( ![C:$i]:
% 0.36/0.54                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.54                  ( ![D:$i]:
% 0.36/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.54                      ( ![E:$i]:
% 0.36/0.54                        ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.54                            ( v1_funct_2 @
% 0.36/0.54                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                            ( m1_subset_1 @
% 0.36/0.54                              E @ 
% 0.36/0.54                              ( k1_zfmisc_1 @
% 0.36/0.54                                ( k2_zfmisc_1 @
% 0.36/0.54                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.36/0.54                            ( ![F:$i]:
% 0.36/0.54                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                                ( ![G:$i]:
% 0.36/0.54                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.54                                    ( ( ( F ) = ( G ) ) =>
% 0.36/0.54                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.36/0.54                                        ( r1_tmap_1 @
% 0.36/0.54                                          C @ B @ 
% 0.36/0.54                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.36/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('2', plain, (((sk_F) = (sk_G))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf(t2_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i]:
% 0.36/0.54         ((r2_hidden @ X3 @ X4)
% 0.36/0.54          | (v1_xboole_0 @ X4)
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.54        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t1_tsep_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.54           ( m1_subset_1 @
% 0.36/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X21 @ X22)
% 0.36/0.54          | (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.54          | ~ (l1_pre_topc @ X22))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_D_1)
% 0.36/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('10', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_m1_pre_topc, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X11 @ X12)
% 0.36/0.54          | (l1_pre_topc @ X11)
% 0.36/0.54          | ~ (l1_pre_topc @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.54  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('14', plain, ((l1_pre_topc @ sk_D_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '14'])).
% 0.36/0.54  thf(t8_connsp_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.54                 ( ?[D:$i]:
% 0.36/0.54                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.36/0.54                     ( v3_pre_topc @ D @ A ) & 
% 0.36/0.54                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.36/0.54          | ~ (r2_hidden @ X14 @ X17)
% 0.36/0.54          | ~ (r1_tarski @ X17 @ X16)
% 0.36/0.54          | ~ (v3_pre_topc @ X17 @ X15)
% 0.36/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.36/0.54          | (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.36/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.36/0.54          | ~ (l1_pre_topc @ X15)
% 0.36/0.54          | ~ (v2_pre_topc @ X15)
% 0.36/0.54          | (v2_struct_0 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_D_1)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_D_1)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_D_1)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.36/0.54          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.36/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D_1)
% 0.36/0.54          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0)
% 0.36/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc1_pre_topc, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X8 @ X9)
% 0.36/0.54          | (v2_pre_topc @ X8)
% 0.36/0.54          | ~ (l1_pre_topc @ X9)
% 0.36/0.54          | ~ (v2_pre_topc @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (v2_pre_topc @ sk_D_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('24', plain, ((v2_pre_topc @ sk_D_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.36/0.54  thf('25', plain, ((l1_pre_topc @ sk_D_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '14'])).
% 0.36/0.54  thf(t16_tsep_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.36/0.54                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X18 @ X19)
% 0.36/0.54          | ((X20) != (u1_struct_0 @ X18))
% 0.36/0.54          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.36/0.54          | ~ (m1_pre_topc @ X18 @ X19)
% 0.36/0.54          | (v3_pre_topc @ X20 @ X19)
% 0.36/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.54          | ~ (l1_pre_topc @ X19)
% 0.36/0.54          | ~ (v2_pre_topc @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i]:
% 0.36/0.54         (~ (v2_pre_topc @ X19)
% 0.36/0.54          | ~ (l1_pre_topc @ X19)
% 0.36/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.36/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.54          | (v3_pre_topc @ (u1_struct_0 @ X18) @ X19)
% 0.36/0.54          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.36/0.54          | ~ (m1_pre_topc @ X18 @ X19))),
% 0.36/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      ((~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.36/0.54        | ~ (v1_tsep_1 @ sk_C @ sk_D_1)
% 0.36/0.54        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D_1)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_D_1)
% 0.36/0.54        | ~ (v2_pre_topc @ sk_D_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '28'])).
% 0.36/0.54  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('31', plain, ((v1_tsep_1 @ sk_C @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('32', plain, ((l1_pre_topc @ sk_D_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('33', plain, ((v2_pre_topc @ sk_D_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.36/0.54  thf('34', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_D_1)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.36/0.54          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.36/0.54          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0)
% 0.36/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '24', '25', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_D_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '35'])).
% 0.36/0.54  thf(d10_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.54  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ sk_D_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['36', '38'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F)
% 0.36/0.54        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '39'])).
% 0.36/0.54  thf('41', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.36/0.54        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F))),
% 0.36/0.54      inference('clc', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.54        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F))),
% 0.36/0.54      inference('sup-', [status(thm)], ['5', '42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '14'])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)
% 0.36/0.54        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('split', [status(esa)], ['45'])).
% 0.36/0.54  thf('47', plain, (((sk_F) = (sk_G))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)
% 0.36/0.54        | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)) | 
% 0.36/0.54       ~
% 0.36/0.54       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))),
% 0.36/0.54      inference('split', [status(esa)], ['49'])).
% 0.36/0.54  thf('51', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('52', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('split', [status(esa)], ['45'])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t81_tmap_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.54                         ( v1_funct_2 @
% 0.36/0.54                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                         ( m1_subset_1 @
% 0.36/0.54                           E @ 
% 0.36/0.54                           ( k1_zfmisc_1 @
% 0.36/0.54                             ( k2_zfmisc_1 @
% 0.36/0.54                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54                       ( ![F:$i]:
% 0.36/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.54                           ( ![G:$i]:
% 0.36/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                               ( ( ( ( F ) = ( G ) ) & 
% 0.36/0.54                                   ( m1_pre_topc @ D @ C ) & 
% 0.36/0.54                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.36/0.54                                 ( r1_tmap_1 @
% 0.36/0.54                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.36/0.54                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X26)
% 0.36/0.54          | ~ (v2_pre_topc @ X26)
% 0.36/0.54          | ~ (l1_pre_topc @ X26)
% 0.36/0.54          | (v2_struct_0 @ X27)
% 0.36/0.54          | ~ (m1_pre_topc @ X27 @ X28)
% 0.36/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.36/0.54          | ~ (m1_pre_topc @ X27 @ X30)
% 0.36/0.54          | ~ (r1_tmap_1 @ X30 @ X26 @ X31 @ X29)
% 0.36/0.54          | ((X29) != (X32))
% 0.36/0.54          | (r1_tmap_1 @ X27 @ X26 @ 
% 0.36/0.54             (k3_tmap_1 @ X28 @ X26 @ X30 @ X27 @ X31) @ X32)
% 0.36/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X27))
% 0.36/0.54          | ~ (m1_subset_1 @ X31 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))))
% 0.36/0.54          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))
% 0.36/0.54          | ~ (v1_funct_1 @ X31)
% 0.36/0.54          | ~ (m1_pre_topc @ X30 @ X28)
% 0.36/0.54          | (v2_struct_0 @ X30)
% 0.36/0.54          | ~ (l1_pre_topc @ X28)
% 0.36/0.54          | ~ (v2_pre_topc @ X28)
% 0.36/0.54          | (v2_struct_0 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X28)
% 0.36/0.54          | ~ (v2_pre_topc @ X28)
% 0.36/0.54          | ~ (l1_pre_topc @ X28)
% 0.36/0.54          | (v2_struct_0 @ X30)
% 0.36/0.54          | ~ (m1_pre_topc @ X30 @ X28)
% 0.36/0.54          | ~ (v1_funct_1 @ X31)
% 0.36/0.54          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))
% 0.36/0.54          | ~ (m1_subset_1 @ X31 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))))
% 0.36/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X27))
% 0.36/0.54          | (r1_tmap_1 @ X27 @ X26 @ 
% 0.36/0.54             (k3_tmap_1 @ X28 @ X26 @ X30 @ X27 @ X31) @ X32)
% 0.36/0.54          | ~ (r1_tmap_1 @ X30 @ X26 @ X31 @ X32)
% 0.36/0.54          | ~ (m1_pre_topc @ X27 @ X30)
% 0.36/0.54          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.36/0.54          | ~ (m1_pre_topc @ X27 @ X28)
% 0.36/0.54          | (v2_struct_0 @ X27)
% 0.36/0.54          | ~ (l1_pre_topc @ X26)
% 0.36/0.54          | ~ (v2_pre_topc @ X26)
% 0.36/0.54          | (v2_struct_0 @ X26))),
% 0.36/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.54          | (v2_struct_0 @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.36/0.54          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.36/0.54          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.36/0.54             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.36/0.54               (u1_struct_0 @ sk_B))
% 0.36/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.36/0.54          | (v2_struct_0 @ sk_D_1)
% 0.36/0.54          | ~ (l1_pre_topc @ X1)
% 0.36/0.54          | ~ (v2_pre_topc @ X1)
% 0.36/0.54          | (v2_struct_0 @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['54', '56'])).
% 0.36/0.54  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B)
% 0.36/0.54          | (v2_struct_0 @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.36/0.54          | ~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X2)
% 0.36/0.54          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.36/0.54             (k3_tmap_1 @ X1 @ sk_B @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.36/0.54          | (v2_struct_0 @ sk_D_1)
% 0.36/0.54          | ~ (l1_pre_topc @ X1)
% 0.36/0.54          | ~ (v2_pre_topc @ X1)
% 0.36/0.54          | (v2_struct_0 @ X1))),
% 0.36/0.54      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i]:
% 0.36/0.54          ((v2_struct_0 @ X0)
% 0.36/0.54           | ~ (v2_pre_topc @ X0)
% 0.36/0.54           | ~ (l1_pre_topc @ X0)
% 0.36/0.54           | (v2_struct_0 @ sk_D_1)
% 0.36/0.54           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.36/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.36/0.54           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.36/0.54              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.36/0.54           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.36/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54           | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.54           | (v2_struct_0 @ X1)
% 0.36/0.54           | (v2_struct_0 @ sk_B)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['53', '62'])).
% 0.36/0.54  thf('64', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      ((![X0 : $i, X1 : $i]:
% 0.36/0.54          ((v2_struct_0 @ X0)
% 0.36/0.54           | ~ (v2_pre_topc @ X0)
% 0.36/0.54           | ~ (l1_pre_topc @ X0)
% 0.36/0.54           | (v2_struct_0 @ sk_D_1)
% 0.36/0.54           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.36/0.54           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.36/0.54           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.36/0.54              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ sk_F)
% 0.36/0.54           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.36/0.54           | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.54           | (v2_struct_0 @ X1)
% 0.36/0.54           | (v2_struct_0 @ sk_B)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          ((v2_struct_0 @ sk_B)
% 0.36/0.54           | (v2_struct_0 @ sk_C)
% 0.36/0.54           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.36/0.54           | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.36/0.54           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.36/0.54           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.36/0.54           | (v2_struct_0 @ sk_D_1)
% 0.36/0.54           | ~ (l1_pre_topc @ X0)
% 0.36/0.54           | ~ (v2_pre_topc @ X0)
% 0.36/0.54           | (v2_struct_0 @ X0)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['52', '65'])).
% 0.36/0.54  thf('67', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          ((v2_struct_0 @ sk_B)
% 0.36/0.54           | (v2_struct_0 @ sk_C)
% 0.36/0.54           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.36/0.54           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54              (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.36/0.54           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.36/0.54           | (v2_struct_0 @ sk_D_1)
% 0.36/0.54           | ~ (l1_pre_topc @ X0)
% 0.36/0.54           | ~ (v2_pre_topc @ X0)
% 0.36/0.54           | (v2_struct_0 @ X0)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.36/0.54  thf('69', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_A)
% 0.36/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.36/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54         | (v2_struct_0 @ sk_D_1)
% 0.36/0.54         | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.36/0.54         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.36/0.54         | (v2_struct_0 @ sk_C)
% 0.36/0.54         | (v2_struct_0 @ sk_B)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['51', '68'])).
% 0.36/0.54  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('72', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('73', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_A)
% 0.36/0.54         | (v2_struct_0 @ sk_D_1)
% 0.36/0.54         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54            (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)
% 0.36/0.54         | (v2_struct_0 @ sk_C)
% 0.36/0.54         | (v2_struct_0 @ sk_B)))
% 0.36/0.54         <= (((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.36/0.54  thf('74', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('split', [status(esa)], ['49'])).
% 0.36/0.54  thf('75', plain, (((sk_F) = (sk_G))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54           (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)))),
% 0.36/0.54      inference('demod', [status(thm)], ['74', '75'])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_B)
% 0.36/0.54         | (v2_struct_0 @ sk_C)
% 0.36/0.54         | (v2_struct_0 @ sk_D_1)
% 0.36/0.54         | (v2_struct_0 @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.36/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['73', '76'])).
% 0.36/0.54  thf('78', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('79', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.36/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.54  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('81', plain,
% 0.36/0.54      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.36/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('clc', [status(thm)], ['79', '80'])).
% 0.36/0.54  thf('82', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('83', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_C))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) & 
% 0.36/0.54             ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('clc', [status(thm)], ['81', '82'])).
% 0.36/0.54  thf('84', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('85', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) | 
% 0.36/0.54       ~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.36/0.54      inference('sup-', [status(thm)], ['83', '84'])).
% 0.36/0.54  thf('86', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G)) | 
% 0.36/0.54       ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.36/0.54      inference('split', [status(esa)], ['45'])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54         (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_G))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['50', '85', '86'])).
% 0.36/0.54  thf('88', plain,
% 0.36/0.54      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.36/0.54        (k3_tmap_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C @ sk_E) @ sk_F)),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['48', '87'])).
% 0.36/0.54  thf('89', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_E @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t83_tmap_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.54                         ( v1_funct_2 @
% 0.36/0.54                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                         ( m1_subset_1 @
% 0.36/0.54                           E @ 
% 0.36/0.54                           ( k1_zfmisc_1 @
% 0.36/0.54                             ( k2_zfmisc_1 @
% 0.36/0.54                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54                       ( ( m1_pre_topc @ C @ D ) =>
% 0.36/0.54                         ( ![F:$i]:
% 0.36/0.54                           ( ( m1_subset_1 @
% 0.36/0.54                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.36/0.54                             ( ![G:$i]:
% 0.36/0.54                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                                 ( ![H:$i]:
% 0.36/0.54                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.54                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.36/0.54                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.36/0.54                                         ( ( G ) = ( H ) ) ) =>
% 0.36/0.54                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.36/0.54                                         ( r1_tmap_1 @
% 0.36/0.54                                           C @ B @ 
% 0.36/0.54                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.36/0.54                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('90', plain,
% 0.36/0.54      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.36/0.54         X40 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X33)
% 0.36/0.54          | ~ (v2_pre_topc @ X33)
% 0.36/0.54          | ~ (l1_pre_topc @ X33)
% 0.36/0.54          | (v2_struct_0 @ X34)
% 0.36/0.54          | ~ (m1_pre_topc @ X34 @ X35)
% 0.36/0.54          | ~ (m1_pre_topc @ X36 @ X34)
% 0.36/0.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.36/0.54          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.36/0.54          | ~ (r1_tmap_1 @ X36 @ X33 @ 
% 0.36/0.54               (k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39) @ X38)
% 0.36/0.54          | (r1_tmap_1 @ X34 @ X33 @ X39 @ X40)
% 0.36/0.54          | ((X40) != (X38))
% 0.36/0.54          | ~ (m1_connsp_2 @ X37 @ X34 @ X40)
% 0.36/0.54          | ~ (r1_tarski @ X37 @ (u1_struct_0 @ X36))
% 0.36/0.54          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X34))
% 0.36/0.54          | ~ (m1_subset_1 @ X39 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.36/0.54          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.36/0.54          | ~ (v1_funct_1 @ X39)
% 0.36/0.54          | ~ (m1_pre_topc @ X36 @ X35)
% 0.36/0.54          | (v2_struct_0 @ X36)
% 0.36/0.54          | ~ (l1_pre_topc @ X35)
% 0.36/0.54          | ~ (v2_pre_topc @ X35)
% 0.36/0.54          | (v2_struct_0 @ X35))),
% 0.36/0.54      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.36/0.54  thf('91', plain,
% 0.36/0.54      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X35)
% 0.36/0.54          | ~ (v2_pre_topc @ X35)
% 0.36/0.54          | ~ (l1_pre_topc @ X35)
% 0.36/0.54          | (v2_struct_0 @ X36)
% 0.36/0.54          | ~ (m1_pre_topc @ X36 @ X35)
% 0.36/0.54          | ~ (v1_funct_1 @ X39)
% 0.36/0.54          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.36/0.54          | ~ (m1_subset_1 @ X39 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 0.36/0.54          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X34))
% 0.36/0.54          | ~ (r1_tarski @ X37 @ (u1_struct_0 @ X36))
% 0.36/0.54          | ~ (m1_connsp_2 @ X37 @ X34 @ X38)
% 0.36/0.54          | (r1_tmap_1 @ X34 @ X33 @ X39 @ X38)
% 0.36/0.54          | ~ (r1_tmap_1 @ X36 @ X33 @ 
% 0.36/0.54               (k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X39) @ X38)
% 0.36/0.54          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.36/0.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.36/0.54          | ~ (m1_pre_topc @ X36 @ X34)
% 0.36/0.54          | ~ (m1_pre_topc @ X34 @ X35)
% 0.36/0.54          | (v2_struct_0 @ X34)
% 0.36/0.54          | ~ (l1_pre_topc @ X33)
% 0.36/0.54          | ~ (v2_pre_topc @ X33)
% 0.36/0.54          | (v2_struct_0 @ X33))),
% 0.36/0.54      inference('simplify', [status(thm)], ['90'])).
% 0.36/0.54  thf('92', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.54          | (v2_struct_0 @ sk_D_1)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.36/0.54          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.36/0.54          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.36/0.54          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.36/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.36/0.54               (u1_struct_0 @ sk_B))
% 0.36/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ X1)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (v2_pre_topc @ X0)
% 0.36/0.54          | (v2_struct_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['89', '91'])).
% 0.36/0.54  thf('93', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('95', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('96', plain, ((v1_funct_1 @ sk_E)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('97', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B)
% 0.36/0.54          | (v2_struct_0 @ sk_D_1)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.36/0.54          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.36/0.54               (k3_tmap_1 @ X0 @ sk_B @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.36/0.54          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ X3)
% 0.36/0.54          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.36/0.54          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.36/0.54          | (v2_struct_0 @ X1)
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | ~ (v2_pre_topc @ X0)
% 0.36/0.54          | (v2_struct_0 @ X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.36/0.54  thf('98', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_C)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.36/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))
% 0.36/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.36/0.54          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.36/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.36/0.54          | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_D_1 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_D_1)
% 0.36/0.54          | (v2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['88', '97'])).
% 0.36/0.54  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('101', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('102', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('103', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('105', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('106', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_C)
% 0.36/0.54          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.36/0.54          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_F)
% 0.36/0.54          | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.36/0.54          | (v2_struct_0 @ sk_D_1)
% 0.36/0.54          | (v2_struct_0 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)],
% 0.36/0.54                ['98', '99', '100', '101', '102', '103', '104', '105'])).
% 0.36/0.54  thf('107', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_B)
% 0.36/0.54        | (v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.36/0.54        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F)
% 0.36/0.54        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['44', '106'])).
% 0.36/0.54  thf('108', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.36/0.54  thf('109', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_B)
% 0.36/0.54        | (v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.36/0.54        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_F)
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['107', '108'])).
% 0.36/0.54  thf('110', plain,
% 0.36/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)
% 0.36/0.54        | (v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (v2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['43', '109'])).
% 0.36/0.54  thf('111', plain,
% 0.36/0.54      ((~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))
% 0.36/0.54         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)))),
% 0.36/0.54      inference('split', [status(esa)], ['49'])).
% 0.36/0.54  thf('112', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['50', '85'])).
% 0.36/0.54  thf('113', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_B @ sk_E @ sk_F)),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['111', '112'])).
% 0.36/0.54  thf('114', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_B)
% 0.36/0.54        | (v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['110', '113'])).
% 0.36/0.54  thf(fc2_struct_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.54  thf('115', plain,
% 0.36/0.54      (![X13 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.36/0.54          | ~ (l1_struct_0 @ X13)
% 0.36/0.54          | (v2_struct_0 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.54  thf('116', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | (v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (v2_struct_0 @ sk_B)
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | ~ (l1_struct_0 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['114', '115'])).
% 0.36/0.54  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('118', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X11 @ X12)
% 0.36/0.54          | (l1_pre_topc @ X11)
% 0.36/0.54          | ~ (l1_pre_topc @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.54  thf('119', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['117', '118'])).
% 0.36/0.54  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('121', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.54      inference('demod', [status(thm)], ['119', '120'])).
% 0.36/0.54  thf(dt_l1_pre_topc, axiom,
% 0.36/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.54  thf('122', plain,
% 0.36/0.54      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.54  thf('123', plain, ((l1_struct_0 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['121', '122'])).
% 0.36/0.54  thf('124', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | (v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (v2_struct_0 @ sk_B)
% 0.36/0.54        | (v2_struct_0 @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['116', '123'])).
% 0.36/0.54  thf('125', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_B)
% 0.36/0.54        | (v2_struct_0 @ sk_D_1)
% 0.36/0.54        | (v2_struct_0 @ sk_C)
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('simplify', [status(thm)], ['124'])).
% 0.36/0.54  thf('126', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('127', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['125', '126'])).
% 0.36/0.54  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('129', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.36/0.54      inference('clc', [status(thm)], ['127', '128'])).
% 0.36/0.54  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('131', plain, ((v2_struct_0 @ sk_C)),
% 0.36/0.54      inference('clc', [status(thm)], ['129', '130'])).
% 0.36/0.54  thf('132', plain, ($false), inference('demod', [status(thm)], ['0', '131'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
