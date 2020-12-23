%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bS9IrhtrqK

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 547 expanded)
%              Number of leaves         :   39 ( 168 expanded)
%              Depth                    :   27
%              Number of atoms          : 2128 (17487 expanded)
%              Number of equality atoms :   11 ( 255 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X17 @ ( k1_connsp_2 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['5','11','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t9_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ( m1_connsp_2 @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 @ X21 )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( X25
       != ( u1_struct_0 @ X23 ) )
      | ~ ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v3_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X23 ) @ X24 )
      | ~ ( v1_tsep_1 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_tsep_1 @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( m1_connsp_2 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32','41'])).

thf('43',plain,
    ( ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ( r1_tarski @ ( sk_D @ X21 @ X19 @ X20 ) @ X19 )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_connsp_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_connsp_2 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('78',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['71'])).

thf('79',plain,(
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

thf('80',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ( X33 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('81',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( r1_tmap_1 @ X28 @ X31 @ X32 @ X30 )
      | ( r1_tmap_1 @ X29 @ X31 @ ( k2_tmap_1 @ X28 @ X31 @ X32 @ X29 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
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
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['75'])).

thf('97',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['71'])).

thf('107',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['76','105','106'])).

thf('108',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['74','107'])).

thf('109',plain,(
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

thf('110',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( r1_tarski @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_connsp_2 @ X37 @ X34 @ X36 )
      | ( X36 != X38 )
      | ~ ( r1_tmap_1 @ X35 @ X39 @ ( k2_tmap_1 @ X34 @ X39 @ X40 @ X35 ) @ X38 )
      | ( r1_tmap_1 @ X34 @ X39 @ X40 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('111',plain,(
    ! [X34: $i,X35: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X35 ) )
      | ( r1_tmap_1 @ X34 @ X39 @ X40 @ X38 )
      | ~ ( r1_tmap_1 @ X35 @ X39 @ ( k2_tmap_1 @ X34 @ X39 @ X40 @ X35 ) @ X38 )
      | ~ ( m1_connsp_2 @ X37 @ X34 @ X38 )
      | ~ ( r1_tarski @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
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
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
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
    inference(demod,[status(thm)],['112','113','114','115','116','117','118'])).

thf('120',plain,(
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
    inference('sup-',[status(thm)],['108','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('122',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['60','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( m1_connsp_2 @ ( sk_D @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(split,[status(esa)],['75'])).

thf('131',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['76','105'])).

thf('132',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('135',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('136',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('138',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['139','140'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('142',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['133','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['0','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bS9IrhtrqK
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 193 iterations in 0.118s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.57  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.57  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(t67_tmap_1, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.57             ( l1_pre_topc @ B ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.57                 ( m1_subset_1 @
% 0.21/0.57                   C @ 
% 0.21/0.57                   ( k1_zfmisc_1 @
% 0.21/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.57               ( ![D:$i]:
% 0.21/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.57                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.57                   ( ![E:$i]:
% 0.21/0.57                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.57                       ( ![F:$i]:
% 0.21/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.57                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.57                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.57                               ( r1_tmap_1 @
% 0.21/0.57                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57            ( l1_pre_topc @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.57                ( l1_pre_topc @ B ) ) =>
% 0.21/0.57              ( ![C:$i]:
% 0.21/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                    ( v1_funct_2 @
% 0.21/0.57                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.57                    ( m1_subset_1 @
% 0.21/0.57                      C @ 
% 0.21/0.57                      ( k1_zfmisc_1 @
% 0.21/0.57                        ( k2_zfmisc_1 @
% 0.21/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.57                  ( ![D:$i]:
% 0.21/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.57                        ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.57                      ( ![E:$i]:
% 0.21/0.57                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.57                          ( ![F:$i]:
% 0.21/0.57                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.57                              ( ( ( E ) = ( F ) ) =>
% 0.21/0.57                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.57                                  ( r1_tmap_1 @
% 0.21/0.57                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.21/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('2', plain, (((sk_E) = (sk_F))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(t30_connsp_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.21/0.57          | (r2_hidden @ X17 @ (k1_connsp_2 @ X18 @ X17))
% 0.21/0.57          | ~ (l1_pre_topc @ X18)
% 0.21/0.57          | ~ (v2_pre_topc @ X18)
% 0.21/0.57          | (v2_struct_0 @ X18))),
% 0.21/0.57      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_D_1)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_D_1)
% 0.21/0.57        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X5 : $i, X6 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.57          | (v2_pre_topc @ X5)
% 0.21/0.57          | ~ (l1_pre_topc @ X6)
% 0.21/0.57          | ~ (v2_pre_topc @ X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      ((~ (v2_pre_topc @ sk_B)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.57        | (v2_pre_topc @ sk_D_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('11', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.57  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_m1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.57  thf('14', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('16', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_D_1)
% 0.21/0.57        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.21/0.57      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.21/0.57  thf('18', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('19', plain, ((r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E))),
% 0.21/0.57      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf('20', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(t2_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ X0 @ X1)
% 0.21/0.57          | (v1_xboole_0 @ X1)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('24', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t1_tsep_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.57           ( m1_subset_1 @
% 0.21/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X26 : $i, X27 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X26 @ X27)
% 0.21/0.57          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.57          | ~ (l1_pre_topc @ X27))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf(t9_connsp_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.57             ( ![C:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.57                      ( ![D:$i]:
% 0.21/0.57                        ( ( m1_subset_1 @
% 0.21/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                          ( ~( ( m1_connsp_2 @ D @ A @ C ) & 
% 0.21/0.57                               ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.57          | ~ (v3_pre_topc @ X19 @ X20)
% 0.21/0.57          | (m1_connsp_2 @ (sk_D @ X21 @ X19 @ X20) @ X20 @ X21)
% 0.21/0.57          | ~ (r2_hidden @ X21 @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.57          | ~ (l1_pre_topc @ X20)
% 0.21/0.57          | ~ (v2_pre_topc @ X20)
% 0.21/0.57          | (v2_struct_0 @ X20))),
% 0.21/0.57      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             sk_B @ X0)
% 0.21/0.57          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf(t16_tsep_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.57                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.57                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X23 @ X24)
% 0.21/0.57          | ((X25) != (u1_struct_0 @ X23))
% 0.21/0.57          | ~ (v1_tsep_1 @ X23 @ X24)
% 0.21/0.57          | ~ (m1_pre_topc @ X23 @ X24)
% 0.21/0.57          | (v3_pre_topc @ X25 @ X24)
% 0.21/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.57          | ~ (l1_pre_topc @ X24)
% 0.21/0.57          | ~ (v2_pre_topc @ X24))),
% 0.21/0.57      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (v2_pre_topc @ X24)
% 0.21/0.57          | ~ (l1_pre_topc @ X24)
% 0.21/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 0.21/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.57          | (v3_pre_topc @ (u1_struct_0 @ X23) @ X24)
% 0.21/0.57          | ~ (v1_tsep_1 @ X23 @ X24)
% 0.21/0.57          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.21/0.57      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.57        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.57        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '35'])).
% 0.21/0.57  thf('37', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('38', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | (m1_connsp_2 @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             sk_B @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['30', '31', '32', '41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (((m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ sk_B @ 
% 0.21/0.57         sk_E)
% 0.21/0.57        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '42'])).
% 0.21/0.57  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57           sk_B @ sk_E))),
% 0.21/0.57      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57           sk_B @ sk_E))),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('48', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.57          | ~ (v3_pre_topc @ X19 @ X20)
% 0.21/0.57          | (r1_tarski @ (sk_D @ X21 @ X19 @ X20) @ X19)
% 0.21/0.57          | ~ (r2_hidden @ X21 @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.57          | ~ (l1_pre_topc @ X20)
% 0.21/0.57          | ~ (v2_pre_topc @ X20)
% 0.21/0.57          | (v2_struct_0 @ X20))),
% 0.21/0.57      inference('cnf', [status(esa)], [t9_connsp_2])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.57  thf('55', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | (r1_tarski @ (sk_D @ X0 @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (((r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57         (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['48', '56'])).
% 0.21/0.57  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57           (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57           (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['47', '59'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57           sk_B @ sk_E))),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '45'])).
% 0.21/0.57  thf('62', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_m1_connsp_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.21/0.57           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X14)
% 0.21/0.57          | ~ (v2_pre_topc @ X14)
% 0.21/0.57          | (v2_struct_0 @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.21/0.57          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.57          | ~ (m1_connsp_2 @ X16 @ X14 @ X15))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.57          | (v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.57          | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.57  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.57          | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.57  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.57          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E))),
% 0.21/0.57      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (m1_subset_1 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.21/0.57        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.21/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.57      inference('split', [status(esa)], ['71'])).
% 0.21/0.57  thf('73', plain, (((sk_E) = (sk_F))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.21/0.57         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)
% 0.21/0.57        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)) | 
% 0.21/0.57       ~
% 0.21/0.57       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.21/0.57      inference('split', [status(esa)], ['75'])).
% 0.21/0.57  thf('77', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.21/0.57         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('split', [status(esa)], ['71'])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t64_tmap_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.57             ( l1_pre_topc @ B ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.57                 ( m1_subset_1 @
% 0.21/0.57                   C @ 
% 0.21/0.57                   ( k1_zfmisc_1 @
% 0.21/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.57               ( ![D:$i]:
% 0.21/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.57                   ( ![E:$i]:
% 0.21/0.57                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.57                       ( ![F:$i]:
% 0.21/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.57                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.57                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.57                             ( r1_tmap_1 @
% 0.21/0.57                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('80', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X28)
% 0.21/0.57          | ~ (v2_pre_topc @ X28)
% 0.21/0.57          | ~ (l1_pre_topc @ X28)
% 0.21/0.57          | (v2_struct_0 @ X29)
% 0.21/0.57          | ~ (m1_pre_topc @ X29 @ X28)
% 0.21/0.57          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.21/0.57          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.21/0.57          | ((X33) != (X30))
% 0.21/0.57          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X33)
% 0.21/0.57          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.21/0.57          | ~ (m1_subset_1 @ X32 @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.21/0.57          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.21/0.57          | ~ (v1_funct_1 @ X32)
% 0.21/0.57          | ~ (l1_pre_topc @ X31)
% 0.21/0.57          | ~ (v2_pre_topc @ X31)
% 0.21/0.57          | (v2_struct_0 @ X31))),
% 0.21/0.57      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X31)
% 0.21/0.57          | ~ (v2_pre_topc @ X31)
% 0.21/0.57          | ~ (l1_pre_topc @ X31)
% 0.21/0.57          | ~ (v1_funct_1 @ X32)
% 0.21/0.57          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))
% 0.21/0.57          | ~ (m1_subset_1 @ X32 @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X31))))
% 0.21/0.57          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.21/0.57          | ~ (r1_tmap_1 @ X28 @ X31 @ X32 @ X30)
% 0.21/0.57          | (r1_tmap_1 @ X29 @ X31 @ (k2_tmap_1 @ X28 @ X31 @ X32 @ X29) @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.21/0.57          | ~ (m1_pre_topc @ X29 @ X28)
% 0.21/0.57          | (v2_struct_0 @ X29)
% 0.21/0.57          | ~ (l1_pre_topc @ X28)
% 0.21/0.57          | ~ (v2_pre_topc @ X28)
% 0.21/0.57          | (v2_struct_0 @ X28))),
% 0.21/0.57      inference('simplify', [status(thm)], ['80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.57          | (v2_struct_0 @ X0)
% 0.21/0.57          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.57          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.21/0.57             X1)
% 0.21/0.57          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.57               (u1_struct_0 @ sk_A))
% 0.21/0.57          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['79', '81'])).
% 0.21/0.57  thf('83', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('86', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | (v2_struct_0 @ X0)
% 0.21/0.57          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.57          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 0.21/0.57             X1)
% 0.21/0.57          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)],
% 0.21/0.57                ['82', '83', '84', '85', '86', '87', '88'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((v2_struct_0 @ sk_A)
% 0.21/0.57           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.57           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.57              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.21/0.57           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.57           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.57           | (v2_struct_0 @ X0)
% 0.21/0.57           | (v2_struct_0 @ sk_B)))
% 0.21/0.57         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['78', '89'])).
% 0.21/0.57  thf('91', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((v2_struct_0 @ sk_A)
% 0.21/0.57           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.57              (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ sk_E)
% 0.21/0.57           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.21/0.57           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.57           | (v2_struct_0 @ X0)
% 0.21/0.57           | (v2_struct_0 @ sk_B)))
% 0.21/0.57         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.57  thf('93', plain,
% 0.21/0.57      ((((v2_struct_0 @ sk_B)
% 0.21/0.57         | (v2_struct_0 @ sk_D_1)
% 0.21/0.57         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.57         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.21/0.57         | (v2_struct_0 @ sk_A)))
% 0.21/0.57         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['77', '92'])).
% 0.21/0.57  thf('94', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      ((((v2_struct_0 @ sk_B)
% 0.21/0.57         | (v2_struct_0 @ sk_D_1)
% 0.21/0.57         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57            (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)
% 0.21/0.57         | (v2_struct_0 @ sk_A)))
% 0.21/0.57         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))
% 0.21/0.57         <= (~
% 0.21/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.57      inference('split', [status(esa)], ['75'])).
% 0.21/0.57  thf('97', plain, (((sk_E) = (sk_F))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('98', plain,
% 0.21/0.57      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57           (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E))
% 0.21/0.57         <= (~
% 0.21/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)))),
% 0.21/0.57      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.57             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['95', '98'])).
% 0.21/0.57  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.57             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.57  thf('102', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_D_1))
% 0.21/0.57         <= (~
% 0.21/0.57             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) & 
% 0.21/0.57             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('clc', [status(thm)], ['101', '102'])).
% 0.21/0.57  thf('104', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.21/0.57       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.57      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F)) | 
% 0.21/0.57       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.57      inference('split', [status(esa)], ['71'])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57         (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_F))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['76', '105', '106'])).
% 0.21/0.57  thf('108', plain,
% 0.21/0.57      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.21/0.57        (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_D_1) @ sk_E)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['74', '107'])).
% 0.21/0.57  thf('109', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t65_tmap_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.57             ( l1_pre_topc @ B ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.57                 ( m1_subset_1 @
% 0.21/0.57                   C @ 
% 0.21/0.57                   ( k1_zfmisc_1 @
% 0.21/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.57               ( ![D:$i]:
% 0.21/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.57                   ( ![E:$i]:
% 0.21/0.57                     ( ( m1_subset_1 @
% 0.21/0.57                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.57                       ( ![F:$i]:
% 0.21/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.57                           ( ![G:$i]:
% 0.21/0.57                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.57                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.21/0.57                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.21/0.57                                   ( ( F ) = ( G ) ) ) =>
% 0.21/0.57                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.21/0.57                                   ( r1_tmap_1 @
% 0.21/0.57                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('110', plain,
% 0.21/0.57      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X34)
% 0.21/0.57          | ~ (v2_pre_topc @ X34)
% 0.21/0.57          | ~ (l1_pre_topc @ X34)
% 0.21/0.57          | (v2_struct_0 @ X35)
% 0.21/0.57          | ~ (m1_pre_topc @ X35 @ X34)
% 0.21/0.57          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 0.21/0.57          | ~ (r1_tarski @ X37 @ (u1_struct_0 @ X35))
% 0.21/0.57          | ~ (m1_connsp_2 @ X37 @ X34 @ X36)
% 0.21/0.57          | ((X36) != (X38))
% 0.21/0.57          | ~ (r1_tmap_1 @ X35 @ X39 @ (k2_tmap_1 @ X34 @ X39 @ X40 @ X35) @ 
% 0.21/0.57               X38)
% 0.21/0.57          | (r1_tmap_1 @ X34 @ X39 @ X40 @ X36)
% 0.21/0.57          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X35))
% 0.21/0.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.21/0.57          | ~ (m1_subset_1 @ X40 @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X39))))
% 0.21/0.57          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X39))
% 0.21/0.57          | ~ (v1_funct_1 @ X40)
% 0.21/0.57          | ~ (l1_pre_topc @ X39)
% 0.21/0.57          | ~ (v2_pre_topc @ X39)
% 0.21/0.57          | (v2_struct_0 @ X39))),
% 0.21/0.57      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.21/0.57  thf('111', plain,
% 0.21/0.57      (![X34 : $i, X35 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.57         ((v2_struct_0 @ X39)
% 0.21/0.57          | ~ (v2_pre_topc @ X39)
% 0.21/0.57          | ~ (l1_pre_topc @ X39)
% 0.21/0.57          | ~ (v1_funct_1 @ X40)
% 0.21/0.57          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X39))
% 0.21/0.57          | ~ (m1_subset_1 @ X40 @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X39))))
% 0.21/0.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.21/0.57          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X35))
% 0.21/0.57          | (r1_tmap_1 @ X34 @ X39 @ X40 @ X38)
% 0.21/0.57          | ~ (r1_tmap_1 @ X35 @ X39 @ (k2_tmap_1 @ X34 @ X39 @ X40 @ X35) @ 
% 0.21/0.57               X38)
% 0.21/0.57          | ~ (m1_connsp_2 @ X37 @ X34 @ X38)
% 0.21/0.57          | ~ (r1_tarski @ X37 @ (u1_struct_0 @ X35))
% 0.21/0.57          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X34))
% 0.21/0.57          | ~ (m1_pre_topc @ X35 @ X34)
% 0.21/0.57          | (v2_struct_0 @ X35)
% 0.21/0.57          | ~ (l1_pre_topc @ X34)
% 0.21/0.57          | ~ (v2_pre_topc @ X34)
% 0.21/0.57          | (v2_struct_0 @ X34))),
% 0.21/0.57      inference('simplify', [status(thm)], ['110'])).
% 0.21/0.57  thf('112', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.57          | (v2_struct_0 @ X0)
% 0.21/0.57          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.57          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.21/0.57          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.57          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.57               (u1_struct_0 @ sk_A))
% 0.21/0.57          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['109', '111'])).
% 0.21/0.57  thf('113', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('115', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('116', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('119', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | (v2_struct_0 @ X0)
% 0.21/0.57          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.21/0.57          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.21/0.57               (k2_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X0) @ X1)
% 0.21/0.57          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ X1)
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.57          | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)],
% 0.21/0.57                ['112', '113', '114', '115', '116', '117', '118'])).
% 0.21/0.57  thf('120', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.57          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.57          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.21/0.57          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.21/0.57          | (v2_struct_0 @ sk_D_1)
% 0.21/0.57          | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['108', '119'])).
% 0.21/0.57  thf('121', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('122', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('123', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('124', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.57          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.57          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.21/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | (v2_struct_0 @ sk_D_1)
% 0.21/0.57          | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.21/0.57  thf('125', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | (v2_struct_0 @ sk_D_1)
% 0.21/0.57        | ~ (r1_tarski @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             sk_B @ sk_E)
% 0.21/0.57        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.57        | (v2_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['70', '124'])).
% 0.21/0.57  thf('126', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (v2_struct_0 @ sk_A)
% 0.21/0.57        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.57        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             sk_B @ sk_E)
% 0.21/0.57        | (v2_struct_0 @ sk_D_1)
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['60', '125'])).
% 0.21/0.57  thf('127', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_B)
% 0.21/0.57        | (v2_struct_0 @ sk_D_1)
% 0.21/0.57        | ~ (m1_connsp_2 @ (sk_D @ sk_E @ (u1_struct_0 @ sk_D_1) @ sk_B) @ 
% 0.21/0.57             sk_B @ sk_E)
% 0.21/0.57        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.57        | (v2_struct_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['126'])).
% 0.21/0.57  thf('128', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (v2_struct_0 @ sk_A)
% 0.21/0.57        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.57        | (v2_struct_0 @ sk_D_1)
% 0.21/0.57        | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '127'])).
% 0.21/0.57  thf('129', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_B)
% 0.21/0.57        | (v2_struct_0 @ sk_D_1)
% 0.21/0.57        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)
% 0.21/0.57        | (v2_struct_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['128'])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))
% 0.21/0.57         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)))),
% 0.21/0.57      inference('split', [status(esa)], ['75'])).
% 0.21/0.57  thf('131', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['76', '105'])).
% 0.21/0.57  thf('132', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C_1 @ sk_E)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['130', '131'])).
% 0.21/0.57  thf('133', plain,
% 0.21/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57        | (v2_struct_0 @ sk_A)
% 0.21/0.57        | (v2_struct_0 @ sk_D_1)
% 0.21/0.57        | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['129', '132'])).
% 0.21/0.57  thf('134', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(dt_k1_connsp_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57       ( m1_subset_1 @
% 0.21/0.57         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.57  thf('135', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X12)
% 0.21/0.57          | ~ (v2_pre_topc @ X12)
% 0.21/0.57          | (v2_struct_0 @ X12)
% 0.21/0.57          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.57          | (m1_subset_1 @ (k1_connsp_2 @ X12 @ X13) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.57  thf('136', plain,
% 0.21/0.57      (((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.21/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.57        | (v2_struct_0 @ sk_D_1)
% 0.21/0.57        | ~ (v2_pre_topc @ sk_D_1)
% 0.21/0.57        | ~ (l1_pre_topc @ sk_D_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['134', '135'])).
% 0.21/0.57  thf('137', plain, ((v2_pre_topc @ sk_D_1)),
% 0.21/0.57      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.57  thf('138', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('139', plain,
% 0.21/0.57      (((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.21/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.57        | (v2_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.21/0.57  thf('140', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('141', plain,
% 0.21/0.57      ((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.21/0.57      inference('clc', [status(thm)], ['139', '140'])).
% 0.21/0.57  thf(t5_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.57  thf('142', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.57          | ~ (v1_xboole_0 @ X4)
% 0.21/0.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.57  thf('143', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['141', '142'])).
% 0.21/0.57  thf('144', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v2_struct_0 @ sk_B)
% 0.21/0.57          | (v2_struct_0 @ sk_D_1)
% 0.21/0.57          | (v2_struct_0 @ sk_A)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['133', '143'])).
% 0.21/0.57  thf('145', plain,
% 0.21/0.57      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '144'])).
% 0.21/0.57  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('147', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.21/0.57      inference('clc', [status(thm)], ['145', '146'])).
% 0.21/0.57  thf('148', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('149', plain, ((v2_struct_0 @ sk_D_1)),
% 0.21/0.57      inference('clc', [status(thm)], ['147', '148'])).
% 0.21/0.57  thf('150', plain, ($false), inference('demod', [status(thm)], ['0', '149'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
