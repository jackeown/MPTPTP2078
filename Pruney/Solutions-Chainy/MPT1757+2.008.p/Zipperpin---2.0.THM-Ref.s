%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dXIu2M4irr

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:54 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  228 (1046 expanded)
%              Number of leaves         :   38 ( 309 expanded)
%              Depth                    :   26
%              Number of atoms          : 2531 (31347 expanded)
%              Number of equality atoms :   13 ( 468 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X31 @ X33 @ ( k2_tmap_1 @ X30 @ X33 @ X34 @ X31 ) @ X32 )
      | ( X35 != X32 )
      | ~ ( r1_tmap_1 @ X30 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_tmap_1 @ X30 @ X33 @ X34 @ X32 )
      | ( r1_tmap_1 @ X31 @ X33 @ ( k2_tmap_1 @ X30 @ X33 @ X34 @ X31 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('34',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['6'])).

thf('44',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['11','42','43'])).

thf('45',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['9','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('47',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tarski @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_connsp_2 @ X39 @ X36 @ X38 )
      | ( X38 != X40 )
      | ~ ( r1_tmap_1 @ X37 @ X41 @ ( k2_tmap_1 @ X36 @ X41 @ X42 @ X37 ) @ X40 )
      | ( r1_tmap_1 @ X36 @ X41 @ X42 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('48',plain,(
    ! [X36: $i,X37: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X37 ) )
      | ( r1_tmap_1 @ X36 @ X41 @ X42 @ X40 )
      | ~ ( r1_tmap_1 @ X37 @ X41 @ ( k2_tmap_1 @ X36 @ X41 @ X42 @ X37 ) @ X40 )
      | ~ ( m1_connsp_2 @ X39 @ X36 @ X40 )
      | ~ ( r1_tarski @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('68',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v3_pre_topc @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('73',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( X27
       != ( u1_struct_0 @ X25 ) )
      | ~ ( v1_tsep_1 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v3_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X25 ) @ X26 )
      | ~ ( v1_tsep_1 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( m1_connsp_2 @ X0 @ sk_B @ X1 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['65','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('89',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('92',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('96',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('101',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('102',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['94','99','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ sk_E ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('110',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_connsp_2 @ ( sk_C @ X17 @ X16 ) @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('111',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('113',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98'])).

thf('114',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['114','115'])).

thf('118',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('119',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_connsp_2 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('122',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('127',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ( r2_hidden @ X21 @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('130',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['116','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('134',plain,
    ( ( r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    r2_hidden @ sk_E @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['114','115'])).

thf('138',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('139',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ( m1_subset_1 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('142',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['137','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('146',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('150',plain,(
    r1_tarski @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('152',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v3_pre_topc @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('155',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98'])).

thf('156',plain,(
    m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['114','115'])).

thf('157',plain,(
    m1_subset_1 @ ( sk_C @ sk_E @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['117','125'])).

thf('158',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ( v3_pre_topc @ ( sk_D @ X23 @ X21 @ X22 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('161',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ X0 @ sk_D_1 ) @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('165',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ sk_D_1 ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['153','154','155','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['150','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ ( sk_C @ sk_E @ sk_D_1 ) @ sk_E @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['136','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_D_1 @ sk_E ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['108','176'])).

thf('178',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ),
    inference(demod,[status(thm)],['87','177'])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','64','178'])).

thf('180',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['10'])).

thf('181',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['11','42'])).

thf('182',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    $false ),
    inference(demod,[status(thm)],['0','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dXIu2M4irr
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 208 iterations in 0.133s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.59  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.59  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.59  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.59  thf(t67_tmap_1, conjecture,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.59             ( l1_pre_topc @ B ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.59                 ( m1_subset_1 @
% 0.38/0.59                   C @ 
% 0.38/0.59                   ( k1_zfmisc_1 @
% 0.38/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.59               ( ![D:$i]:
% 0.38/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.38/0.59                     ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.59                   ( ![E:$i]:
% 0.38/0.59                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.59                       ( ![F:$i]:
% 0.38/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.59                           ( ( ( E ) = ( F ) ) =>
% 0.38/0.59                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.38/0.59                               ( r1_tmap_1 @
% 0.38/0.59                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i]:
% 0.38/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.59            ( l1_pre_topc @ A ) ) =>
% 0.38/0.59          ( ![B:$i]:
% 0.38/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.59                ( l1_pre_topc @ B ) ) =>
% 0.38/0.59              ( ![C:$i]:
% 0.38/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.59                    ( v1_funct_2 @
% 0.38/0.59                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.59                    ( m1_subset_1 @
% 0.38/0.59                      C @ 
% 0.38/0.59                      ( k1_zfmisc_1 @
% 0.38/0.59                        ( k2_zfmisc_1 @
% 0.38/0.59                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.59                  ( ![D:$i]:
% 0.38/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.38/0.59                        ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.59                      ( ![E:$i]:
% 0.38/0.59                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.59                          ( ![F:$i]:
% 0.38/0.59                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.59                              ( ( ( E ) = ( F ) ) =>
% 0.38/0.59                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.38/0.59                                  ( r1_tmap_1 @
% 0.38/0.59                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.38/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t1_tsep_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.59           ( m1_subset_1 @
% 0.38/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X28 : $i, X29 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X28 @ X29)
% 0.38/0.59          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.59          | ~ (l1_pre_topc @ X29))),
% 0.38/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.38/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf('4', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.38/0.59        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.38/0.59         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.59      inference('split', [status(esa)], ['6'])).
% 0.38/0.59  thf('8', plain, (((sk_E) = (sk_F))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.38/0.59         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.38/0.59        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.38/0.59       ~
% 0.38/0.59       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.38/0.59      inference('split', [status(esa)], ['10'])).
% 0.38/0.59  thf('12', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('13', plain, (((sk_E) = (sk_F))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('14', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.38/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('split', [status(esa)], ['6'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.59        (k1_zfmisc_1 @ 
% 0.38/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t64_tmap_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.59             ( l1_pre_topc @ B ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.59                 ( m1_subset_1 @
% 0.38/0.59                   C @ 
% 0.38/0.59                   ( k1_zfmisc_1 @
% 0.38/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.59               ( ![D:$i]:
% 0.38/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.59                   ( ![E:$i]:
% 0.38/0.59                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.59                       ( ![F:$i]:
% 0.38/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.59                           ( ( ( ( E ) = ( F ) ) & 
% 0.38/0.59                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.38/0.59                             ( r1_tmap_1 @
% 0.38/0.59                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X30)
% 0.38/0.59          | ~ (v2_pre_topc @ X30)
% 0.38/0.59          | ~ (l1_pre_topc @ X30)
% 0.38/0.59          | (v2_struct_0 @ X31)
% 0.38/0.59          | ~ (m1_pre_topc @ X31 @ X30)
% 0.38/0.59          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.38/0.59          | (r1_tmap_1 @ X31 @ X33 @ (k2_tmap_1 @ X30 @ X33 @ X34 @ X31) @ X32)
% 0.38/0.59          | ((X35) != (X32))
% 0.38/0.59          | ~ (r1_tmap_1 @ X30 @ X33 @ X34 @ X35)
% 0.38/0.59          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X30))
% 0.38/0.59          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))))
% 0.38/0.59          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))
% 0.38/0.59          | ~ (v1_funct_1 @ X34)
% 0.38/0.59          | ~ (l1_pre_topc @ X33)
% 0.38/0.59          | ~ (v2_pre_topc @ X33)
% 0.38/0.59          | (v2_struct_0 @ X33))),
% 0.38/0.59      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X33)
% 0.38/0.59          | ~ (v2_pre_topc @ X33)
% 0.38/0.59          | ~ (l1_pre_topc @ X33)
% 0.38/0.59          | ~ (v1_funct_1 @ X34)
% 0.38/0.59          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))
% 0.38/0.59          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))))
% 0.38/0.59          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.38/0.59          | ~ (r1_tmap_1 @ X30 @ X33 @ X34 @ X32)
% 0.38/0.59          | (r1_tmap_1 @ X31 @ X33 @ (k2_tmap_1 @ X30 @ X33 @ X34 @ X31) @ X32)
% 0.38/0.59          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.38/0.59          | ~ (m1_pre_topc @ X31 @ X30)
% 0.38/0.59          | (v2_struct_0 @ X31)
% 0.38/0.59          | ~ (l1_pre_topc @ X30)
% 0.38/0.59          | ~ (v2_pre_topc @ X30)
% 0.38/0.59          | (v2_struct_0 @ X30))),
% 0.38/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.59          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.38/0.59             X1)
% 0.38/0.59          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.59               (u1_struct_0 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['16', '18'])).
% 0.38/0.59  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('23', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.59          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.38/0.59             X1)
% 0.38/0.59          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)],
% 0.38/0.59                ['19', '20', '21', '22', '23', '24', '25'])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          ((v2_struct_0 @ sk_A)
% 0.38/0.59           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.59           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.59              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.38/0.59           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.38/0.59           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.59           | (v2_struct_0 @ X0)
% 0.38/0.59           | (v2_struct_0 @ sk_B)))
% 0.38/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['15', '26'])).
% 0.38/0.59  thf('28', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      ((![X0 : $i]:
% 0.38/0.59          ((v2_struct_0 @ sk_A)
% 0.38/0.59           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.59              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.38/0.59           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.38/0.59           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.59           | (v2_struct_0 @ X0)
% 0.38/0.59           | (v2_struct_0 @ sk_B)))
% 0.38/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      ((((v2_struct_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_D_1)
% 0.38/0.59         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.59         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.38/0.59         | (v2_struct_0 @ sk_A)))
% 0.38/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['14', '29'])).
% 0.38/0.59  thf('31', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      ((((v2_struct_0 @ sk_B)
% 0.38/0.59         | (v2_struct_0 @ sk_D_1)
% 0.38/0.59         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.38/0.59         | (v2_struct_0 @ sk_A)))
% 0.38/0.59         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.59      inference('split', [status(esa)], ['10'])).
% 0.38/0.59  thf('34', plain, (((sk_E) = (sk_F))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.38/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.38/0.59             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['32', '35'])).
% 0.38/0.59  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.38/0.59             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('clc', [status(thm)], ['36', '37'])).
% 0.38/0.59  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_D_1))
% 0.38/0.59         <= (~
% 0.38/0.59             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.38/0.59             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.59      inference('clc', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('41', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.38/0.59       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.38/0.59       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.59      inference('split', [status(esa)], ['6'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.38/0.59      inference('sat_resolution*', [status(thm)], ['11', '42', '43'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.59        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)),
% 0.38/0.59      inference('simpl_trail', [status(thm)], ['9', '44'])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.59        (k1_zfmisc_1 @ 
% 0.38/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t65_tmap_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.59             ( l1_pre_topc @ B ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.59                 ( m1_subset_1 @
% 0.38/0.59                   C @ 
% 0.38/0.59                   ( k1_zfmisc_1 @
% 0.38/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.59               ( ![D:$i]:
% 0.38/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.59                   ( ![E:$i]:
% 0.38/0.59                     ( ( m1_subset_1 @
% 0.38/0.59                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.59                       ( ![F:$i]:
% 0.38/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.59                           ( ![G:$i]:
% 0.38/0.59                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.59                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.38/0.59                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.38/0.59                                   ( ( F ) = ( G ) ) ) =>
% 0.38/0.59                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.38/0.59                                   ( r1_tmap_1 @
% 0.38/0.59                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X36)
% 0.38/0.59          | ~ (v2_pre_topc @ X36)
% 0.38/0.59          | ~ (l1_pre_topc @ X36)
% 0.38/0.59          | (v2_struct_0 @ X37)
% 0.38/0.59          | ~ (m1_pre_topc @ X37 @ X36)
% 0.38/0.59          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.38/0.59          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X37))
% 0.38/0.59          | ~ (m1_connsp_2 @ X39 @ X36 @ X38)
% 0.38/0.59          | ((X38) != (X40))
% 0.38/0.59          | ~ (r1_tmap_1 @ X37 @ X41 @ (k2_tmap_1 @ X36 @ X41 @ X42 @ X37) @ 
% 0.38/0.59               X40)
% 0.38/0.59          | (r1_tmap_1 @ X36 @ X41 @ X42 @ X38)
% 0.38/0.59          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.38/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.38/0.59          | ~ (m1_subset_1 @ X42 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))))
% 0.38/0.59          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))
% 0.38/0.59          | ~ (v1_funct_1 @ X42)
% 0.38/0.59          | ~ (l1_pre_topc @ X41)
% 0.38/0.59          | ~ (v2_pre_topc @ X41)
% 0.38/0.59          | (v2_struct_0 @ X41))),
% 0.38/0.59      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X36 : $i, X37 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X41)
% 0.38/0.59          | ~ (v2_pre_topc @ X41)
% 0.38/0.59          | ~ (l1_pre_topc @ X41)
% 0.38/0.59          | ~ (v1_funct_1 @ X42)
% 0.38/0.59          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))
% 0.38/0.59          | ~ (m1_subset_1 @ X42 @ 
% 0.38/0.59               (k1_zfmisc_1 @ 
% 0.38/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))))
% 0.38/0.59          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.38/0.59          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.38/0.59          | (r1_tmap_1 @ X36 @ X41 @ X42 @ X40)
% 0.38/0.59          | ~ (r1_tmap_1 @ X37 @ X41 @ (k2_tmap_1 @ X36 @ X41 @ X42 @ X37) @ 
% 0.38/0.59               X40)
% 0.38/0.59          | ~ (m1_connsp_2 @ X39 @ X36 @ X40)
% 0.38/0.59          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X37))
% 0.38/0.59          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X36))
% 0.38/0.59          | ~ (m1_pre_topc @ X37 @ X36)
% 0.38/0.59          | (v2_struct_0 @ X37)
% 0.38/0.59          | ~ (l1_pre_topc @ X36)
% 0.38/0.59          | ~ (v2_pre_topc @ X36)
% 0.38/0.59          | (v2_struct_0 @ X36))),
% 0.38/0.59      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.38/0.59          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.38/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.59          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.59               (u1_struct_0 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.59          | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['46', '48'])).
% 0.38/0.59  thf('50', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ X0)
% 0.38/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.38/0.59          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.59               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.38/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.59          | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)],
% 0.38/0.59                ['49', '50', '51', '52', '53', '54', '55'])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.59          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.59          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.38/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.59          | (v2_struct_0 @ sk_D_1)
% 0.38/0.59          | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['45', '56'])).
% 0.38/0.59  thf('58', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('59', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('60', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('61', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.59          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.59          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.38/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | (v2_struct_0 @ sk_D_1)
% 0.38/0.59          | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_B)
% 0.38/0.59        | (v2_struct_0 @ sk_D_1)
% 0.38/0.59        | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.38/0.59        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.59        | (v2_struct_0 @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '61'])).
% 0.38/0.59  thf(d10_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.59      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.59  thf('65', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('66', plain,
% 0.38/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf('67', plain,
% 0.38/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf(t8_connsp_2, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.38/0.59                 ( ?[D:$i]:
% 0.38/0.59                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.38/0.59                     ( v3_pre_topc @ D @ A ) & 
% 0.38/0.59                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.38/0.59          | ~ (r2_hidden @ X21 @ X24)
% 0.38/0.59          | ~ (r1_tarski @ X24 @ X23)
% 0.38/0.59          | ~ (v3_pre_topc @ X24 @ X22)
% 0.38/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.59          | (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.38/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.59          | ~ (l1_pre_topc @ X22)
% 0.38/0.59          | ~ (v2_pre_topc @ X22)
% 0.38/0.59          | (v2_struct_0 @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.38/0.59  thf('69', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.59          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.38/0.59          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.38/0.59          | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ X0)
% 0.38/0.59          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.59  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('72', plain,
% 0.38/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf(t16_tsep_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.59                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.38/0.59                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.38/0.59  thf('73', plain,
% 0.38/0.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X25 @ X26)
% 0.38/0.59          | ((X27) != (u1_struct_0 @ X25))
% 0.38/0.59          | ~ (v1_tsep_1 @ X25 @ X26)
% 0.38/0.59          | ~ (m1_pre_topc @ X25 @ X26)
% 0.38/0.59          | (v3_pre_topc @ X27 @ X26)
% 0.38/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.59          | ~ (l1_pre_topc @ X26)
% 0.38/0.59          | ~ (v2_pre_topc @ X26))),
% 0.38/0.59      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.38/0.59  thf('74', plain,
% 0.38/0.59      (![X25 : $i, X26 : $i]:
% 0.38/0.59         (~ (v2_pre_topc @ X26)
% 0.38/0.59          | ~ (l1_pre_topc @ X26)
% 0.38/0.59          | ~ (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.38/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.59          | (v3_pre_topc @ (u1_struct_0 @ X25) @ X26)
% 0.38/0.59          | ~ (v1_tsep_1 @ X25 @ X26)
% 0.38/0.59          | ~ (m1_pre_topc @ X25 @ X26))),
% 0.38/0.59      inference('simplify', [status(thm)], ['73'])).
% 0.38/0.59  thf('75', plain,
% 0.38/0.59      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.59        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.38/0.59        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['72', '74'])).
% 0.38/0.59  thf('76', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('77', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('80', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.38/0.59      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.38/0.59  thf('81', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_B)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.59          | (m1_connsp_2 @ X0 @ sk_B @ X1)
% 0.38/0.59          | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ X0)
% 0.38/0.59          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['69', '70', '71', '80'])).
% 0.38/0.59  thf('82', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | ~ (r1_tarski @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.59          | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['66', '81'])).
% 0.38/0.59  thf('83', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.59      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.59  thf('84', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.38/0.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.59          | (v2_struct_0 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.38/0.59  thf('85', plain,
% 0.38/0.59      (((v2_struct_0 @ sk_B)
% 0.38/0.59        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.38/0.59        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['65', '84'])).
% 0.38/0.59  thf('86', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('87', plain,
% 0.38/0.59      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.38/0.59      inference('clc', [status(thm)], ['85', '86'])).
% 0.38/0.59  thf('88', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('89', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.59      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.59  thf(t3_subset, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.59  thf('90', plain,
% 0.38/0.59      (![X3 : $i, X5 : $i]:
% 0.38/0.59         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.59  thf('91', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.59  thf(t6_connsp_2, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]:
% 0.38/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59           ( ![C:$i]:
% 0.38/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.59               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.59  thf('92', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.59          | ~ (m1_connsp_2 @ X18 @ X19 @ X20)
% 0.38/0.59          | (r2_hidden @ X20 @ X18)
% 0.38/0.59          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.38/0.59          | ~ (l1_pre_topc @ X19)
% 0.38/0.59          | ~ (v2_pre_topc @ X19)
% 0.38/0.59          | (v2_struct_0 @ X19))),
% 0.38/0.59      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.38/0.59  thf('93', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((v2_struct_0 @ X0)
% 0.38/0.59          | ~ (v2_pre_topc @ X0)
% 0.38/0.59          | ~ (l1_pre_topc @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.59          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.59          | ~ (m1_connsp_2 @ (u1_struct_0 @ X0) @ X0 @ X1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['91', '92'])).
% 0.38/0.59  thf('94', plain,
% 0.38/0.59      ((~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.38/0.59        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59        | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.59        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['88', '93'])).
% 0.38/0.59  thf('95', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_m1_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( l1_pre_topc @ A ) =>
% 0.38/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.59  thf('96', plain,
% 0.38/0.59      (![X8 : $i, X9 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.59  thf('97', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.59  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('99', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.59  thf('100', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(cc1_pre_topc, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.59  thf('101', plain,
% 0.38/0.59      (![X6 : $i, X7 : $i]:
% 0.38/0.59         (~ (m1_pre_topc @ X6 @ X7)
% 0.38/0.59          | (v2_pre_topc @ X6)
% 0.38/0.59          | ~ (l1_pre_topc @ X7)
% 0.38/0.59          | ~ (v2_pre_topc @ X7))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.59  thf('102', plain,
% 0.38/0.59      ((~ (v2_pre_topc @ sk_B)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.59        | (v2_pre_topc @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['100', '101'])).
% 0.38/0.59  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('105', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.59  thf('106', plain,
% 0.38/0.59      ((~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.38/0.59        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['94', '99', '105'])).
% 0.38/0.59  thf('107', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('108', plain,
% 0.38/0.59      (((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ sk_E))),
% 0.38/0.59      inference('clc', [status(thm)], ['106', '107'])).
% 0.38/0.59  thf('109', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf(existence_m1_connsp_2, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.59         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.38/0.59  thf('110', plain,
% 0.38/0.59      (![X16 : $i, X17 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X16)
% 0.38/0.59          | ~ (v2_pre_topc @ X16)
% 0.38/0.59          | (v2_struct_0 @ X16)
% 0.38/0.59          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.38/0.59          | (m1_connsp_2 @ (sk_C @ X17 @ X16) @ X16 @ X17))),
% 0.38/0.59      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.38/0.59  thf('111', plain,
% 0.38/0.59      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.38/0.59        | (v2_struct_0 @ sk_D_1)
% 0.38/0.59        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.59        | ~ (l1_pre_topc @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['109', '110'])).
% 0.38/0.59  thf('112', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.59  thf('113', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.59  thf('114', plain,
% 0.38/0.59      (((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.38/0.59        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.38/0.59  thf('115', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('116', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.59      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.59  thf('117', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.59      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.59  thf('118', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf(dt_m1_connsp_2, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.59         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.59       ( ![C:$i]:
% 0.38/0.59         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.38/0.59           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.59  thf('119', plain,
% 0.38/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.59         (~ (l1_pre_topc @ X13)
% 0.38/0.59          | ~ (v2_pre_topc @ X13)
% 0.38/0.59          | (v2_struct_0 @ X13)
% 0.38/0.59          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.38/0.59          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.59          | ~ (m1_connsp_2 @ X15 @ X13 @ X14))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.38/0.59  thf('120', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.38/0.59          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.59          | (v2_struct_0 @ sk_D_1)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['118', '119'])).
% 0.38/0.59  thf('121', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.59  thf('122', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.59  thf('123', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E)
% 0.38/0.59          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.59          | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.38/0.59  thf('124', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('125', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.59          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_E))),
% 0.38/0.59      inference('clc', [status(thm)], ['123', '124'])).
% 0.38/0.59  thf('126', plain,
% 0.38/0.59      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['117', '125'])).
% 0.38/0.59  thf('127', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.38/0.59          | ~ (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.38/0.59          | (r2_hidden @ X21 @ (sk_D @ X23 @ X21 @ X22))
% 0.38/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.59          | ~ (l1_pre_topc @ X22)
% 0.38/0.59          | ~ (v2_pre_topc @ X22)
% 0.38/0.59          | (v2_struct_0 @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.38/0.59  thf('128', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_D_1)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.59          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1))
% 0.38/0.59          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['126', '127'])).
% 0.38/0.59  thf('129', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.59  thf('130', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.59  thf('131', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_D_1)
% 0.38/0.59          | (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1))
% 0.38/0.59          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.38/0.59  thf('132', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59        | (r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.59        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['116', '131'])).
% 0.38/0.59  thf('133', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('134', plain,
% 0.38/0.59      (((r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.59        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['132', '133'])).
% 0.38/0.59  thf('135', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('136', plain,
% 0.38/0.59      ((r2_hidden @ sk_E @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))),
% 0.38/0.59      inference('clc', [status(thm)], ['134', '135'])).
% 0.38/0.59  thf('137', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.59      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.59  thf('138', plain,
% 0.38/0.59      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['117', '125'])).
% 0.38/0.59  thf('139', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.38/0.59          | ~ (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.38/0.59          | (m1_subset_1 @ (sk_D @ X23 @ X21 @ X22) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.59          | ~ (l1_pre_topc @ X22)
% 0.38/0.59          | ~ (v2_pre_topc @ X22)
% 0.38/0.59          | (v2_struct_0 @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.38/0.59  thf('140', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_D_1)
% 0.38/0.59          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.59          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.59          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.59          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['138', '139'])).
% 0.38/0.59  thf('141', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.59  thf('142', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.59      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.59  thf('143', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((v2_struct_0 @ sk_D_1)
% 0.38/0.59          | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.59          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.59      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.38/0.59  thf('144', plain,
% 0.38/0.59      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.59        | (m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.59        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['137', '143'])).
% 0.38/0.59  thf('145', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.59  thf('146', plain,
% 0.38/0.59      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.59        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['144', '145'])).
% 0.38/0.59  thf('147', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('148', plain,
% 0.38/0.59      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('clc', [status(thm)], ['146', '147'])).
% 0.38/0.60  thf('149', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i]:
% 0.38/0.60         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('150', plain,
% 0.38/0.60      ((r1_tarski @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['148', '149'])).
% 0.38/0.60  thf('151', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('clc', [status(thm)], ['146', '147'])).
% 0.38/0.60  thf('152', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.38/0.60          | ~ (r2_hidden @ X21 @ X24)
% 0.38/0.60          | ~ (r1_tarski @ X24 @ X23)
% 0.38/0.60          | ~ (v3_pre_topc @ X24 @ X22)
% 0.38/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.60          | (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.38/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.60          | ~ (l1_pre_topc @ X22)
% 0.38/0.60          | ~ (v2_pre_topc @ X22)
% 0.38/0.60          | (v2_struct_0 @ X22))),
% 0.38/0.60      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.38/0.60  thf('153', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.38/0.60          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60               sk_D_1)
% 0.38/0.60          | ~ (r1_tarski @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ X0)
% 0.38/0.60          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['151', '152'])).
% 0.38/0.60  thf('154', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.60  thf('155', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.60  thf('156', plain, ((m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.60  thf('157', plain,
% 0.38/0.60      ((m1_subset_1 @ (sk_C @ sk_E @ sk_D_1) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['117', '125'])).
% 0.38/0.60  thf('158', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.38/0.60          | ~ (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ X23 @ X21 @ X22) @ X22)
% 0.38/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.60          | ~ (l1_pre_topc @ X22)
% 0.38/0.60          | ~ (v2_pre_topc @ X22)
% 0.38/0.60          | (v2_struct_0 @ X22))),
% 0.38/0.60      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.38/0.60  thf('159', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.60          | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['157', '158'])).
% 0.38/0.60  thf('160', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.60  thf('161', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.60      inference('demod', [status(thm)], ['97', '98'])).
% 0.38/0.60  thf('162', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ X0 @ sk_D_1) @ 
% 0.38/0.60             sk_D_1)
% 0.38/0.60          | ~ (m1_connsp_2 @ (sk_C @ sk_E @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.38/0.60  thf('163', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ 
% 0.38/0.60           sk_D_1)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['156', '162'])).
% 0.38/0.60  thf('164', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.60  thf('165', plain,
% 0.38/0.60      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ sk_D_1)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['163', '164'])).
% 0.38/0.60  thf('166', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('167', plain,
% 0.38/0.60      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ sk_D_1)),
% 0.38/0.60      inference('clc', [status(thm)], ['165', '166'])).
% 0.38/0.60  thf('168', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((v2_struct_0 @ sk_D_1)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.38/0.60          | ~ (r1_tarski @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1) @ X0)
% 0.38/0.60          | ~ (r2_hidden @ X1 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('demod', [status(thm)], ['153', '154', '155', '167'])).
% 0.38/0.60  thf('169', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.60               (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.60          | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['150', '168'])).
% 0.38/0.60  thf('170', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.60  thf('171', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.60          | ~ (r2_hidden @ X0 @ (sk_D @ (sk_C @ sk_E @ sk_D_1) @ sk_E @ sk_D_1))
% 0.38/0.60          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ X0)
% 0.38/0.60          | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['169', '170'])).
% 0.38/0.60  thf('172', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_D_1)
% 0.38/0.60        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ sk_E)
% 0.38/0.60        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['136', '171'])).
% 0.38/0.60  thf('173', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.60  thf('174', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_D_1)
% 0.38/0.60        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ sk_E))),
% 0.38/0.60      inference('demod', [status(thm)], ['172', '173'])).
% 0.38/0.60  thf('175', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('176', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_D_1 @ sk_E)),
% 0.38/0.60      inference('clc', [status(thm)], ['174', '175'])).
% 0.38/0.60  thf('177', plain, ((r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('demod', [status(thm)], ['108', '176'])).
% 0.38/0.60  thf('178', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)),
% 0.38/0.60      inference('demod', [status(thm)], ['87', '177'])).
% 0.38/0.60  thf('179', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_B)
% 0.38/0.60        | (v2_struct_0 @ sk_D_1)
% 0.38/0.60        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.38/0.60        | (v2_struct_0 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['62', '64', '178'])).
% 0.38/0.60  thf('180', plain,
% 0.38/0.60      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.38/0.60         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.38/0.60      inference('split', [status(esa)], ['10'])).
% 0.38/0.60  thf('181', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['11', '42'])).
% 0.38/0.60  thf('182', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['180', '181'])).
% 0.38/0.60  thf('183', plain,
% 0.38/0.60      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['179', '182'])).
% 0.38/0.60  thf('184', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('185', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.38/0.60      inference('clc', [status(thm)], ['183', '184'])).
% 0.38/0.60  thf('186', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('187', plain, ((v2_struct_0 @ sk_D_1)),
% 0.38/0.60      inference('clc', [status(thm)], ['185', '186'])).
% 0.38/0.60  thf('188', plain, ($false), inference('demod', [status(thm)], ['0', '187'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
