%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wWlhnxO9ap

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:56 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 344 expanded)
%              Number of leaves         :   36 ( 110 expanded)
%              Depth                    :   26
%              Number of atoms          : 1665 (11038 expanded)
%              Number of equality atoms :   13 ( 161 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t67_tmap_1,conjecture,(
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
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

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
                      & ( v1_tsep_1 @ D @ B )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ( ( E = F )
                             => ( ( r1_tmap_1 @ B @ A @ C @ E )
                              <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
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
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( m1_connsp_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ~ ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v3_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_tsep_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('32',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('39',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['32'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X21 @ X23 @ ( k2_tmap_1 @ X20 @ X23 @ X24 @ X21 ) @ X22 )
      | ( X25 != X22 )
      | ~ ( r1_tmap_1 @ X20 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_tmap_1 @ X20 @ X23 @ X24 @ X22 )
      | ( r1_tmap_1 @ X21 @ X23 @ ( k2_tmap_1 @ X20 @ X23 @ X24 @ X21 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('58',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['32'])).

thf('68',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['37','66','67'])).

thf('69',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['35','68'])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X28 )
      | ( X28 != X30 )
      | ~ ( r1_tmap_1 @ X27 @ X31 @ ( k2_tmap_1 @ X26 @ X31 @ X32 @ X27 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X31 @ X32 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('72',plain,(
    ! [X26: $i,X27: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X26 @ X31 @ X32 @ X30 )
      | ~ ( r1_tmap_1 @ X27 @ X31 @ ( k2_tmap_1 @ X26 @ X31 @ X32 @ X27 ) @ X30 )
      | ~ ( m1_connsp_2 @ X29 @ X26 @ X30 )
      | ~ ( r1_tarski @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
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
    inference(demod,[status(thm)],['73','74','75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','85'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','89'])).

thf('91',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['36'])).

thf('92',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['37','66'])).

thf('93',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('95',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('98',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['99','100'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('102',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('103',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['96','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['0','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wWlhnxO9ap
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:01:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 71 iterations in 0.047s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.54  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.36/0.54  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.36/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.54  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.54  thf(t67_tmap_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54             ( l1_pre_topc @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.54                 ( m1_subset_1 @
% 0.36/0.54                   C @ 
% 0.36/0.54                   ( k1_zfmisc_1 @
% 0.36/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.36/0.54                     ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.54                   ( ![E:$i]:
% 0.36/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                       ( ![F:$i]:
% 0.36/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                           ( ( ( E ) = ( F ) ) =>
% 0.36/0.54                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.36/0.54                               ( r1_tmap_1 @
% 0.36/0.54                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.54            ( l1_pre_topc @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.54                ( l1_pre_topc @ B ) ) =>
% 0.36/0.54              ( ![C:$i]:
% 0.36/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                    ( v1_funct_2 @
% 0.36/0.54                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.54                    ( m1_subset_1 @
% 0.36/0.54                      C @ 
% 0.36/0.54                      ( k1_zfmisc_1 @
% 0.36/0.54                        ( k2_zfmisc_1 @
% 0.36/0.54                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.54                  ( ![D:$i]:
% 0.36/0.54                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.36/0.54                        ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.54                      ( ![E:$i]:
% 0.36/0.54                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                          ( ![F:$i]:
% 0.36/0.54                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.54                              ( ( ( E ) = ( F ) ) =>
% 0.36/0.54                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.36/0.54                                  ( r1_tmap_1 @
% 0.36/0.54                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.36/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('2', plain, (((sk_E) = (sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
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
% 0.36/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.54        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t1_tsep_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.54           ( m1_subset_1 @
% 0.36/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X18 @ X19)
% 0.36/0.54          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.54          | ~ (l1_pre_topc @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.36/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf(t5_connsp_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.36/0.54                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.54          | ~ (v3_pre_topc @ X12 @ X13)
% 0.36/0.54          | ~ (r2_hidden @ X14 @ X12)
% 0.36/0.54          | (m1_connsp_2 @ X12 @ X13 @ X14)
% 0.36/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.36/0.54          | ~ (l1_pre_topc @ X13)
% 0.36/0.54          | ~ (v2_pre_topc @ X13)
% 0.36/0.54          | (v2_struct_0 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.36/0.54          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ X0)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.36/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf('14', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.36/0.54          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ X0)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.36/0.54          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '10'])).
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
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X15 @ X16)
% 0.36/0.54          | ((X17) != (u1_struct_0 @ X15))
% 0.36/0.54          | ~ (v1_tsep_1 @ X15 @ X16)
% 0.36/0.54          | ~ (m1_pre_topc @ X15 @ X16)
% 0.36/0.54          | (v3_pre_topc @ X17 @ X16)
% 0.36/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.54          | ~ (l1_pre_topc @ X16)
% 0.36/0.54          | ~ (v2_pre_topc @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X15 : $i, X16 : $i]:
% 0.36/0.54         (~ (v2_pre_topc @ X16)
% 0.36/0.54          | ~ (l1_pre_topc @ X16)
% 0.36/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.36/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.54          | (v3_pre_topc @ (u1_struct_0 @ X15) @ X16)
% 0.36/0.54          | ~ (v1_tsep_1 @ X15 @ X16)
% 0.36/0.54          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.36/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.36/0.55        | ~ (v1_tsep_1 @ sk_D @ sk_B)
% 0.36/0.55        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '19'])).
% 0.36/0.55  thf('21', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('22', plain, ((v1_tsep_1 @ sk_D @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('24', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('25', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.36/0.55          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ X0)
% 0.36/0.55          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['16', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.36/0.55        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ sk_E)
% 0.36/0.55        | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['6', '26'])).
% 0.36/0.55  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (((m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ sk_E)
% 0.36/0.55        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.36/0.55      inference('clc', [status(thm)], ['27', '28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.55        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ sk_E))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55         sk_F)
% 0.36/0.55        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55         sk_F))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.36/0.55      inference('split', [status(esa)], ['32'])).
% 0.36/0.55  thf('34', plain, (((sk_E) = (sk_F))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55         sk_E))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.36/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55           sk_F)
% 0.36/0.55        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.36/0.55       ~
% 0.36/0.55       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55         sk_F))),
% 0.36/0.55      inference('split', [status(esa)], ['36'])).
% 0.36/0.55  thf('38', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('split', [status(esa)], ['32'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t64_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                 ( m1_subset_1 @
% 0.36/0.55                   C @ 
% 0.36/0.55                   ( k1_zfmisc_1 @
% 0.36/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.55                   ( ![E:$i]:
% 0.36/0.55                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.55                       ( ![F:$i]:
% 0.36/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.55                           ( ( ( ( E ) = ( F ) ) & 
% 0.36/0.55                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.36/0.55                             ( r1_tmap_1 @
% 0.36/0.55                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X20)
% 0.36/0.55          | ~ (v2_pre_topc @ X20)
% 0.36/0.55          | ~ (l1_pre_topc @ X20)
% 0.36/0.55          | (v2_struct_0 @ X21)
% 0.36/0.55          | ~ (m1_pre_topc @ X21 @ X20)
% 0.36/0.55          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.36/0.55          | (r1_tmap_1 @ X21 @ X23 @ (k2_tmap_1 @ X20 @ X23 @ X24 @ X21) @ X22)
% 0.36/0.55          | ((X25) != (X22))
% 0.36/0.55          | ~ (r1_tmap_1 @ X20 @ X23 @ X24 @ X25)
% 0.36/0.55          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X20))
% 0.36/0.55          | ~ (m1_subset_1 @ X24 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))))
% 0.36/0.55          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))
% 0.36/0.55          | ~ (v1_funct_1 @ X24)
% 0.36/0.55          | ~ (l1_pre_topc @ X23)
% 0.36/0.55          | ~ (v2_pre_topc @ X23)
% 0.36/0.55          | (v2_struct_0 @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X23)
% 0.36/0.55          | ~ (v2_pre_topc @ X23)
% 0.36/0.55          | ~ (l1_pre_topc @ X23)
% 0.36/0.55          | ~ (v1_funct_1 @ X24)
% 0.36/0.55          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))
% 0.36/0.55          | ~ (m1_subset_1 @ X24 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23))))
% 0.36/0.55          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.36/0.55          | ~ (r1_tmap_1 @ X20 @ X23 @ X24 @ X22)
% 0.36/0.55          | (r1_tmap_1 @ X21 @ X23 @ (k2_tmap_1 @ X20 @ X23 @ X24 @ X21) @ X22)
% 0.36/0.55          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.36/0.55          | ~ (m1_pre_topc @ X21 @ X20)
% 0.36/0.55          | (v2_struct_0 @ X21)
% 0.36/0.55          | ~ (l1_pre_topc @ X20)
% 0.36/0.55          | ~ (v2_pre_topc @ X20)
% 0.36/0.55          | (v2_struct_0 @ X20))),
% 0.36/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.36/0.55          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['40', '42'])).
% 0.36/0.55  thf('44', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.55          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.36/0.55          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['43', '44', '45', '46', '47', '48', '49'])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      ((![X0 : $i]:
% 0.36/0.55          ((v2_struct_0 @ sk_A)
% 0.36/0.55           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.36/0.55           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.36/0.55              sk_E)
% 0.36/0.55           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.36/0.55           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55           | (v2_struct_0 @ X0)
% 0.36/0.55           | (v2_struct_0 @ sk_B)))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '50'])).
% 0.36/0.55  thf('52', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      ((![X0 : $i]:
% 0.36/0.55          ((v2_struct_0 @ sk_A)
% 0.36/0.55           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.36/0.55              sk_E)
% 0.36/0.55           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.36/0.55           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55           | (v2_struct_0 @ X0)
% 0.36/0.55           | (v2_struct_0 @ sk_B)))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_B)
% 0.36/0.55         | (v2_struct_0 @ sk_D)
% 0.36/0.55         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.36/0.55         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.36/0.55         | (v2_struct_0 @ sk_A)))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['38', '53'])).
% 0.36/0.55  thf('55', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_B)
% 0.36/0.55         | (v2_struct_0 @ sk_D)
% 0.36/0.55         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.36/0.55         | (v2_struct_0 @ sk_A)))
% 0.36/0.55         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55           sk_F))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.36/0.55      inference('split', [status(esa)], ['36'])).
% 0.36/0.55  thf('58', plain, (((sk_E) = (sk_F))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55           sk_E))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.36/0.55      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.36/0.55             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['56', '59'])).
% 0.36/0.55  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.36/0.55             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('clc', [status(thm)], ['60', '61'])).
% 0.36/0.55  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('64', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_D))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.36/0.55               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.36/0.55             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('clc', [status(thm)], ['62', '63'])).
% 0.36/0.55  thf('65', plain, (~ (v2_struct_0 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55         sk_F)) | 
% 0.36/0.55       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.36/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55         sk_F)) | 
% 0.36/0.55       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.36/0.55      inference('split', [status(esa)], ['32'])).
% 0.36/0.55  thf('68', plain,
% 0.36/0.55      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55         sk_F))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['37', '66', '67'])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.36/0.55        sk_E)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['35', '68'])).
% 0.36/0.55  thf('70', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t65_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                 ( m1_subset_1 @
% 0.36/0.55                   C @ 
% 0.36/0.55                   ( k1_zfmisc_1 @
% 0.36/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.36/0.55                   ( ![E:$i]:
% 0.36/0.55                     ( ( m1_subset_1 @
% 0.36/0.55                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.55                       ( ![F:$i]:
% 0.36/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.55                           ( ![G:$i]:
% 0.36/0.55                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.36/0.55                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.36/0.55                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.36/0.55                                   ( ( F ) = ( G ) ) ) =>
% 0.36/0.55                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.36/0.55                                   ( r1_tmap_1 @
% 0.36/0.55                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('71', plain,
% 0.36/0.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X26)
% 0.36/0.55          | ~ (v2_pre_topc @ X26)
% 0.36/0.55          | ~ (l1_pre_topc @ X26)
% 0.36/0.55          | (v2_struct_0 @ X27)
% 0.36/0.55          | ~ (m1_pre_topc @ X27 @ X26)
% 0.36/0.55          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.36/0.55          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (m1_connsp_2 @ X29 @ X26 @ X28)
% 0.36/0.55          | ((X28) != (X30))
% 0.36/0.55          | ~ (r1_tmap_1 @ X27 @ X31 @ (k2_tmap_1 @ X26 @ X31 @ X32 @ X27) @ 
% 0.36/0.55               X30)
% 0.36/0.55          | (r1_tmap_1 @ X26 @ X31 @ X32 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.55          | ~ (m1_subset_1 @ X32 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))))
% 0.36/0.55          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))
% 0.36/0.55          | ~ (v1_funct_1 @ X32)
% 0.36/0.55          | ~ (l1_pre_topc @ X31)
% 0.36/0.55          | ~ (v2_pre_topc @ X31)
% 0.36/0.55          | (v2_struct_0 @ X31))),
% 0.36/0.55      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.36/0.55  thf('72', plain,
% 0.36/0.55      (![X26 : $i, X27 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X31)
% 0.36/0.55          | ~ (v2_pre_topc @ X31)
% 0.36/0.55          | ~ (l1_pre_topc @ X31)
% 0.36/0.55          | ~ (v1_funct_1 @ X32)
% 0.36/0.55          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))
% 0.36/0.55          | ~ (m1_subset_1 @ X32 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X31))))
% 0.36/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 0.36/0.55          | (r1_tmap_1 @ X26 @ X31 @ X32 @ X30)
% 0.36/0.55          | ~ (r1_tmap_1 @ X27 @ X31 @ (k2_tmap_1 @ X26 @ X31 @ X32 @ X27) @ 
% 0.36/0.55               X30)
% 0.36/0.55          | ~ (m1_connsp_2 @ X29 @ X26 @ X30)
% 0.36/0.55          | ~ (r1_tarski @ X29 @ (u1_struct_0 @ X27))
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.36/0.55          | ~ (m1_pre_topc @ X27 @ X26)
% 0.36/0.55          | (v2_struct_0 @ X27)
% 0.36/0.55          | ~ (l1_pre_topc @ X26)
% 0.36/0.55          | ~ (v2_pre_topc @ X26)
% 0.36/0.55          | (v2_struct_0 @ X26))),
% 0.36/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.36/0.55  thf('73', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.36/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.36/0.55               X1)
% 0.36/0.55          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['70', '72'])).
% 0.36/0.55  thf('74', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('76', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('80', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_B)
% 0.36/0.55          | (v2_struct_0 @ X0)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.36/0.55          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.36/0.55          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.36/0.55               X1)
% 0.36/0.55          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['73', '74', '75', '76', '77', '78', '79'])).
% 0.36/0.55  thf('81', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.55          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))
% 0.36/0.55          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.36/0.55          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.36/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.36/0.55          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.36/0.55          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.36/0.55          | (v2_struct_0 @ sk_D)
% 0.36/0.55          | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['69', '80'])).
% 0.36/0.55  thf('82', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf('83', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('85', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.36/0.55          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.36/0.55          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.36/0.55          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.36/0.55          | (v2_struct_0 @ sk_D)
% 0.36/0.55          | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.36/0.55  thf('86', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.36/0.55        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ sk_E)
% 0.36/0.55        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '85'])).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('87', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('88', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.55      inference('simplify', [status(thm)], ['87'])).
% 0.36/0.55  thf('89', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B @ sk_E)
% 0.36/0.55        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['86', '88'])).
% 0.36/0.55  thf('90', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['30', '89'])).
% 0.36/0.55  thf('91', plain,
% 0.36/0.55      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.36/0.55         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.36/0.55      inference('split', [status(esa)], ['36'])).
% 0.36/0.55  thf('92', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['37', '66'])).
% 0.36/0.55  thf('93', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.36/0.55  thf('94', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['90', '93'])).
% 0.36/0.55  thf(fc2_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('95', plain,
% 0.36/0.55      (![X8 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.36/0.55          | ~ (l1_struct_0 @ X8)
% 0.36/0.55          | (v2_struct_0 @ X8))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.55  thf('96', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | ~ (l1_struct_0 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.36/0.55  thf('97', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_m1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.55  thf('98', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('99', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.36/0.55  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('101', plain, ((l1_pre_topc @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['99', '100'])).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('102', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('103', plain, ((l1_struct_0 @ sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.36/0.55  thf('104', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | (v2_struct_0 @ sk_D)
% 0.36/0.55        | (v2_struct_0 @ sk_B)
% 0.36/0.55        | (v2_struct_0 @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['96', '103'])).
% 0.36/0.55  thf('105', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('simplify', [status(thm)], ['104'])).
% 0.36/0.55  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('107', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.36/0.55      inference('clc', [status(thm)], ['105', '106'])).
% 0.36/0.55  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('109', plain, ((v2_struct_0 @ sk_D)),
% 0.36/0.55      inference('clc', [status(thm)], ['107', '108'])).
% 0.36/0.55  thf('110', plain, ($false), inference('demod', [status(thm)], ['0', '109'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
