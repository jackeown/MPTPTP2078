%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ByWaMJyaLh

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 497 expanded)
%              Number of leaves         :   30 ( 151 expanded)
%              Depth                    :   28
%              Number of atoms          : 1711 (19030 expanded)
%              Number of equality atoms :   16 ( 259 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t66_tmap_1,conjecture,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ( ( ( v3_pre_topc @ E @ B )
                                    & ( r2_hidden @ F @ E )
                                    & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                    & ( F = G ) )
                                 => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                  <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( m1_connsp_2 @ E @ B @ F )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_tarski @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_connsp_2 @ X17 @ X14 @ X16 )
      | ( X16 != X18 )
      | ~ ( r1_tmap_1 @ X14 @ X19 @ X20 @ X16 )
      | ( r1_tmap_1 @ X15 @ X19 @ ( k2_tmap_1 @ X14 @ X19 @ X20 @ X15 ) @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( r1_tmap_1 @ X15 @ X19 @ ( k2_tmap_1 @ X14 @ X19 @ X20 @ X15 ) @ X18 )
      | ~ ( r1_tmap_1 @ X14 @ X19 @ X20 @ X18 )
      | ~ ( m1_connsp_2 @ X17 @ X14 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_connsp_2 @ sk_E @ sk_B @ X1 )
      | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ ( k1_tops_1 @ X9 @ X10 ) )
      | ( m1_connsp_2 @ X10 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_B @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X4 @ X3 ) @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_E ) @ sk_E ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_E ) @ sk_E ),
    inference(demod,[status(thm)],['38','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) )
    | ( sk_E
      = ( k1_tops_1 @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_tops_1 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 )
      | ~ ( v3_pre_topc @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ sk_E @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_E @ sk_E )
    | ( r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r1_tarski @ sk_E @ ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['50','52'])).

thf('54',plain,
    ( sk_E
    = ( k1_tops_1 @ sk_B @ sk_E ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ sk_E @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_G @ sk_E )
    | ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','55'])).

thf('57',plain,(
    r2_hidden @ sk_F @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ sk_G @ sk_E ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_G )
        | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['26','29','62'])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['8','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('78',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['7','76','77'])).

thf('79',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['3','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r1_tarski @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_connsp_2 @ X17 @ X14 @ X16 )
      | ( X16 != X18 )
      | ~ ( r1_tmap_1 @ X15 @ X19 @ ( k2_tmap_1 @ X14 @ X19 @ X20 @ X15 ) @ X18 )
      | ( r1_tmap_1 @ X14 @ X19 @ X20 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('82',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ( r1_tmap_1 @ X14 @ X19 @ X20 @ X18 )
      | ~ ( r1_tmap_1 @ X15 @ X19 @ ( k2_tmap_1 @ X14 @ X19 @ X20 @ X15 ) @ X18 )
      | ~ ( m1_connsp_2 @ X17 @ X14 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('94',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_G )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_connsp_2 @ sk_E @ sk_B @ sk_G )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','95'])).

thf('97',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_connsp_2 @ sk_E @ sk_B @ sk_G ),
    inference(clc,[status(thm)],['60','61'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['68'])).

thf('101',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['2'])).

thf('104',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['7','76','107'])).

thf('109',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['102','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ByWaMJyaLh
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 16:45:53 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 67 iterations in 0.031s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(t66_tmap_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                 ( m1_subset_1 @
% 0.22/0.51                   C @ 
% 0.22/0.51                   ( k1_zfmisc_1 @
% 0.22/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.51                   ( ![E:$i]:
% 0.22/0.51                     ( ( m1_subset_1 @
% 0.22/0.51                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                       ( ![F:$i]:
% 0.22/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                           ( ![G:$i]:
% 0.22/0.51                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.51                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.22/0.51                                   ( r2_hidden @ F @ E ) & 
% 0.22/0.51                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.51                                   ( ( F ) = ( G ) ) ) =>
% 0.22/0.51                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.51                                   ( r1_tmap_1 @
% 0.22/0.51                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51            ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51                ( l1_pre_topc @ B ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                    ( v1_funct_2 @
% 0.22/0.51                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                    ( m1_subset_1 @
% 0.22/0.51                      C @ 
% 0.22/0.51                      ( k1_zfmisc_1 @
% 0.22/0.51                        ( k2_zfmisc_1 @
% 0.22/0.51                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51                  ( ![D:$i]:
% 0.22/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.51                      ( ![E:$i]:
% 0.22/0.51                        ( ( m1_subset_1 @
% 0.22/0.51                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                          ( ![F:$i]:
% 0.22/0.51                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                              ( ![G:$i]:
% 0.22/0.51                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.51                                  ( ( ( v3_pre_topc @ E @ B ) & 
% 0.22/0.51                                      ( r2_hidden @ F @ E ) & 
% 0.22/0.51                                      ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.51                                      ( ( F ) = ( G ) ) ) =>
% 0.22/0.51                                    ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.51                                      ( r1_tmap_1 @
% 0.22/0.51                                        D @ A @ 
% 0.22/0.51                                        ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t66_tmap_1])).
% 0.22/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51           sk_G)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('5', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51           sk_G)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.22/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)) | 
% 0.22/0.51       ~
% 0.22/0.51       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G))),
% 0.22/0.51      inference('split', [status(esa)], ['6'])).
% 0.22/0.51  thf('8', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('10', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t65_tmap_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                 ( m1_subset_1 @
% 0.22/0.51                   C @ 
% 0.22/0.51                   ( k1_zfmisc_1 @
% 0.22/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.51                   ( ![E:$i]:
% 0.22/0.51                     ( ( m1_subset_1 @
% 0.22/0.51                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                       ( ![F:$i]:
% 0.22/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                           ( ![G:$i]:
% 0.22/0.51                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.51                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.51                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.22/0.51                                   ( ( F ) = ( G ) ) ) =>
% 0.22/0.51                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.51                                   ( r1_tmap_1 @
% 0.22/0.51                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X14)
% 0.22/0.51          | ~ (v2_pre_topc @ X14)
% 0.22/0.51          | ~ (l1_pre_topc @ X14)
% 0.22/0.51          | (v2_struct_0 @ X15)
% 0.22/0.51          | ~ (m1_pre_topc @ X15 @ X14)
% 0.22/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.22/0.51          | ~ (r1_tarski @ X17 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_connsp_2 @ X17 @ X14 @ X16)
% 0.22/0.51          | ((X16) != (X18))
% 0.22/0.51          | ~ (r1_tmap_1 @ X14 @ X19 @ X20 @ X16)
% 0.22/0.51          | (r1_tmap_1 @ X15 @ X19 @ (k2_tmap_1 @ X14 @ X19 @ X20 @ X15) @ X18)
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (m1_subset_1 @ X20 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))))
% 0.22/0.51          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))
% 0.22/0.51          | ~ (v1_funct_1 @ X20)
% 0.22/0.51          | ~ (l1_pre_topc @ X19)
% 0.22/0.51          | ~ (v2_pre_topc @ X19)
% 0.22/0.51          | (v2_struct_0 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X19)
% 0.22/0.51          | ~ (v2_pre_topc @ X19)
% 0.22/0.51          | ~ (l1_pre_topc @ X19)
% 0.22/0.51          | ~ (v1_funct_1 @ X20)
% 0.22/0.51          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))
% 0.22/0.51          | ~ (m1_subset_1 @ X20 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))))
% 0.22/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | (r1_tmap_1 @ X15 @ X19 @ (k2_tmap_1 @ X14 @ X19 @ X20 @ X15) @ X18)
% 0.22/0.51          | ~ (r1_tmap_1 @ X14 @ X19 @ X20 @ X18)
% 0.22/0.51          | ~ (m1_connsp_2 @ X17 @ X14 @ X18)
% 0.22/0.51          | ~ (r1_tarski @ X17 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X14))
% 0.22/0.51          | ~ (m1_pre_topc @ X15 @ X14)
% 0.22/0.51          | (v2_struct_0 @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X14)
% 0.22/0.51          | ~ (v2_pre_topc @ X14)
% 0.22/0.51          | (v2_struct_0 @ X14))),
% 0.22/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ X0)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.22/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.51          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.51  thf('18', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ X0)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.22/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.51          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)],
% 0.22/0.51                ['17', '18', '19', '20', '21', '22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.51          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.22/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.51          | ~ (m1_connsp_2 @ sk_E @ sk_B @ X1)
% 0.22/0.51          | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      ((![X0 : $i]:
% 0.22/0.51          ((v2_struct_0 @ sk_B)
% 0.22/0.51           | (v2_struct_0 @ X0)
% 0.22/0.51           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.22/0.51           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.22/0.51           | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.22/0.51           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.51              sk_G)
% 0.22/0.51           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.22/0.51           | (v2_struct_0 @ sk_A)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '25'])).
% 0.22/0.51  thf('27', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('30', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d1_connsp_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.22/0.51                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.22/0.51          | ~ (r2_hidden @ X8 @ (k1_tops_1 @ X9 @ X10))
% 0.22/0.51          | (m1_connsp_2 @ X10 @ X9 @ X8)
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.51          | ~ (l1_pre_topc @ X9)
% 0.22/0.51          | ~ (v2_pre_topc @ X9)
% 0.22/0.51          | (v2_struct_0 @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_B @ sk_E))
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t44_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.51          | (r1_tarski @ (k1_tops_1 @ X4 @ X3) @ X3)
% 0.22/0.51          | ~ (l1_pre_topc @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_B) | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_E) @ sk_E))),
% 0.22/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain, ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_E) @ sk_E)),
% 0.22/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf(d10_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i]:
% 0.22/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      ((~ (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E))
% 0.22/0.51        | ((sk_E) = (k1_tops_1 @ sk_B @ sk_E)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t56_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.51          | ~ (v3_pre_topc @ X5 @ X6)
% 0.22/0.51          | ~ (r1_tarski @ X5 @ X7)
% 0.22/0.51          | (r1_tarski @ X5 @ (k1_tops_1 @ X6 @ X7))
% 0.22/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.51          | ~ (l1_pre_topc @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_B)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.22/0.51          | ~ (r1_tarski @ sk_E @ X0)
% 0.22/0.51          | ~ (v3_pre_topc @ sk_E @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.51  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('48', plain, ((v3_pre_topc @ sk_E @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ X0))
% 0.22/0.51          | ~ (r1_tarski @ sk_E @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      ((~ (r1_tarski @ sk_E @ sk_E)
% 0.22/0.51        | (r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['43', '49'])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.51  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.51      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.51  thf('53', plain, ((r1_tarski @ sk_E @ (k1_tops_1 @ sk_B @ sk_E))),
% 0.22/0.51      inference('demod', [status(thm)], ['50', '52'])).
% 0.22/0.51  thf('54', plain, (((sk_E) = (k1_tops_1 @ sk_B @ sk_E))),
% 0.22/0.51      inference('demod', [status(thm)], ['42', '53'])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | (m1_connsp_2 @ sk_E @ sk_B @ X0)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ sk_E)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['33', '34', '35', '54'])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      ((~ (r2_hidden @ sk_G @ sk_E)
% 0.22/0.51        | (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.22/0.51        | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['30', '55'])).
% 0.22/0.51  thf('57', plain, ((r2_hidden @ sk_F @ sk_E)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('58', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('59', plain, ((r2_hidden @ sk_G @ sk_E)),
% 0.22/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (((m1_connsp_2 @ sk_E @ sk_B @ sk_G) | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['56', '59'])).
% 0.22/0.51  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('62', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.22/0.51      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      ((![X0 : $i]:
% 0.22/0.51          ((v2_struct_0 @ sk_B)
% 0.22/0.51           | (v2_struct_0 @ X0)
% 0.22/0.51           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51           | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ X0))
% 0.22/0.51           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.51              sk_G)
% 0.22/0.51           | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.22/0.51           | (v2_struct_0 @ sk_A)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['26', '29', '62'])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A)
% 0.22/0.51         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.22/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.51            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)
% 0.22/0.51         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.51         | (v2_struct_0 @ sk_D)
% 0.22/0.51         | (v2_struct_0 @ sk_B)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '63'])).
% 0.22/0.51  thf('65', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('66', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A)
% 0.22/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.51            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)
% 0.22/0.51         | (v2_struct_0 @ sk_D)
% 0.22/0.51         | (v2_struct_0 @ sk_B)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51           sk_G)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51           sk_G))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['68'])).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['67', '69'])).
% 0.22/0.51  thf('71', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('clc', [status(thm)], ['70', '71'])).
% 0.22/0.51  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_D))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.51               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_G)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('clc', [status(thm)], ['72', '73'])).
% 0.22/0.51  thf('75', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('76', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G)) | 
% 0.22/0.51       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.22/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.51  thf('77', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.22/0.51      inference('split', [status(esa)], ['11'])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51         sk_G))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['7', '76', '77'])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.51        sk_G)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['3', '78'])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('81', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X14)
% 0.22/0.51          | ~ (v2_pre_topc @ X14)
% 0.22/0.51          | ~ (l1_pre_topc @ X14)
% 0.22/0.51          | (v2_struct_0 @ X15)
% 0.22/0.51          | ~ (m1_pre_topc @ X15 @ X14)
% 0.22/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 0.22/0.51          | ~ (r1_tarski @ X17 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_connsp_2 @ X17 @ X14 @ X16)
% 0.22/0.51          | ((X16) != (X18))
% 0.22/0.51          | ~ (r1_tmap_1 @ X15 @ X19 @ (k2_tmap_1 @ X14 @ X19 @ X20 @ X15) @ 
% 0.22/0.51               X18)
% 0.22/0.51          | (r1_tmap_1 @ X14 @ X19 @ X20 @ X16)
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (m1_subset_1 @ X20 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))))
% 0.22/0.51          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))
% 0.22/0.51          | ~ (v1_funct_1 @ X20)
% 0.22/0.51          | ~ (l1_pre_topc @ X19)
% 0.22/0.51          | ~ (v2_pre_topc @ X19)
% 0.22/0.51          | (v2_struct_0 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.22/0.51  thf('82', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X19)
% 0.22/0.51          | ~ (v2_pre_topc @ X19)
% 0.22/0.51          | ~ (l1_pre_topc @ X19)
% 0.22/0.51          | ~ (v1_funct_1 @ X20)
% 0.22/0.51          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))
% 0.22/0.51          | ~ (m1_subset_1 @ X20 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X19))))
% 0.22/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.22/0.51          | (r1_tmap_1 @ X14 @ X19 @ X20 @ X18)
% 0.22/0.51          | ~ (r1_tmap_1 @ X15 @ X19 @ (k2_tmap_1 @ X14 @ X19 @ X20 @ X15) @ 
% 0.22/0.51               X18)
% 0.22/0.51          | ~ (m1_connsp_2 @ X17 @ X14 @ X18)
% 0.22/0.51          | ~ (r1_tarski @ X17 @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X14))
% 0.22/0.51          | ~ (m1_pre_topc @ X15 @ X14)
% 0.22/0.51          | (v2_struct_0 @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X14)
% 0.22/0.51          | ~ (v2_pre_topc @ X14)
% 0.22/0.51          | (v2_struct_0 @ X14))),
% 0.22/0.51      inference('simplify', [status(thm)], ['81'])).
% 0.22/0.51  thf('83', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ X0)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.22/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.51               X1)
% 0.22/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['80', '82'])).
% 0.22/0.51  thf('84', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('86', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('90', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ X0)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.22/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.51               X1)
% 0.22/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)],
% 0.22/0.51                ['83', '84', '85', '86', '87', '88', '89'])).
% 0.22/0.51  thf('91', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.22/0.51          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['79', '90'])).
% 0.22/0.51  thf('92', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('93', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf('94', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('95', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.22/0.51          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_G)
% 0.22/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.22/0.51  thf('96', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | ~ (r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))
% 0.22/0.51        | ~ (m1_connsp_2 @ sk_E @ sk_B @ sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '95'])).
% 0.22/0.51  thf('97', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('98', plain, ((m1_connsp_2 @ sk_E @ sk_B @ sk_G)),
% 0.22/0.51      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.51  thf('99', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.22/0.51  thf('100', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['68'])).
% 0.22/0.51  thf('101', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('102', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.22/0.51      inference('demod', [status(thm)], ['100', '101'])).
% 0.22/0.51  thf('103', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('104', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('105', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)))),
% 0.22/0.51      inference('demod', [status(thm)], ['103', '104'])).
% 0.22/0.51  thf('106', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['6'])).
% 0.22/0.51  thf('107', plain,
% 0.22/0.51      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G))),
% 0.22/0.51      inference('sup-', [status(thm)], ['105', '106'])).
% 0.22/0.51  thf('108', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_F))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['7', '76', '107'])).
% 0.22/0.51  thf('109', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_G)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['102', '108'])).
% 0.22/0.51  thf('110', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['99', '109'])).
% 0.22/0.51  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('112', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.22/0.51      inference('clc', [status(thm)], ['110', '111'])).
% 0.22/0.51  thf('113', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('114', plain, ((v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('clc', [status(thm)], ['112', '113'])).
% 0.22/0.51  thf('115', plain, ($false), inference('demod', [status(thm)], ['0', '114'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
