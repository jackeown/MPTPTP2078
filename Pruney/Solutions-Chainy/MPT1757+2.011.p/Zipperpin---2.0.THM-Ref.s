%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.go7aaNPJHe

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:55 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 615 expanded)
%              Number of leaves         :   39 ( 187 expanded)
%              Depth                    :   27
%              Number of atoms          : 2271 (19594 expanded)
%              Number of equality atoms :   11 ( 283 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ( m1_connsp_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
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

thf('35',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X25 ) @ X26 )
      | ~ ( v1_tsep_1 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X26 ) ) ),
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
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t7_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( m1_connsp_2 @ ( sk_D @ X24 @ X22 @ X23 ) @ X23 @ X22 )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('59',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('60',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r1_tarski @ ( sk_D @ X24 @ X22 @ X23 ) @ X24 )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('71',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( m1_subset_1 @ ( sk_D @ X24 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_connsp_2 @ X24 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_connsp_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D_1 ) @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('89',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['82'])).

thf('90',plain,(
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

thf('91',plain,(
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

thf('92',plain,(
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
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
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
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97','98','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['89','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(split,[status(esa)],['86'])).

thf('108',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['82'])).

thf('118',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['87','116','117'])).

thf('119',plain,(
    r1_tmap_1 @ sk_D_1 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['85','118'])).

thf('120',plain,(
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

thf('121',plain,(
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

thf('122',plain,(
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
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
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
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
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
    inference(demod,[status(thm)],['123','124','125','126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('133',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['69','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( m1_connsp_2 @ ( sk_D @ ( u1_struct_0 @ sk_D_1 ) @ sk_E @ sk_B ) @ sk_B @ sk_E )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['86'])).

thf('142',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['87','116'])).

thf('143',plain,(
    ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('146',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('147',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('149',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('150',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('153',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['144','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_struct_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['0','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.go7aaNPJHe
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:29:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 155 iterations in 0.113s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.58  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.38/0.58  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.58  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.58  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.58  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.38/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.58  thf(t67_tmap_1, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                 ( m1_subset_1 @
% 0.38/0.58                   C @ 
% 0.38/0.58                   ( k1_zfmisc_1 @
% 0.38/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.38/0.58                     ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                       ( ![F:$i]:
% 0.38/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.58                           ( ( ( E ) = ( F ) ) =>
% 0.38/0.58                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.38/0.58                               ( r1_tmap_1 @
% 0.38/0.58                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58            ( l1_pre_topc @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58                ( l1_pre_topc @ B ) ) =>
% 0.38/0.58              ( ![C:$i]:
% 0.38/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                    ( v1_funct_2 @
% 0.38/0.58                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                    ( m1_subset_1 @
% 0.38/0.58                      C @ 
% 0.38/0.58                      ( k1_zfmisc_1 @
% 0.38/0.58                        ( k2_zfmisc_1 @
% 0.38/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58                  ( ![D:$i]:
% 0.38/0.58                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.38/0.58                        ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.58                      ( ![E:$i]:
% 0.38/0.58                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                          ( ![F:$i]:
% 0.38/0.58                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.58                              ( ( ( E ) = ( F ) ) =>
% 0.38/0.58                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.38/0.58                                  ( r1_tmap_1 @
% 0.38/0.58                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.38/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('2', plain, (((sk_E) = (sk_F))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf(t30_connsp_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.38/0.58          | (r2_hidden @ X17 @ (k1_connsp_2 @ X18 @ X17))
% 0.38/0.58          | ~ (l1_pre_topc @ X18)
% 0.38/0.58          | ~ (v2_pre_topc @ X18)
% 0.38/0.58          | (v2_struct_0 @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_D_1)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_D_1)
% 0.38/0.58        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.58  thf('6', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X5 @ X6)
% 0.38/0.58          | (v2_pre_topc @ X5)
% 0.38/0.58          | ~ (l1_pre_topc @ X6)
% 0.38/0.58          | ~ (v2_pre_topc @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      ((~ (v2_pre_topc @ sk_B)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58        | (v2_pre_topc @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('11', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.58  thf('12', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_m1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X7 : $i, X8 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.58  thf('14', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('16', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.38/0.58      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.38/0.58  thf('18', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('19', plain, ((r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D_1 @ sk_E))),
% 0.38/0.58      inference('clc', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf(t2_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r2_hidden @ X0 @ X1)
% 0.38/0.58          | (v1_xboole_0 @ X1)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf('23', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('24', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t1_tsep_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( m1_subset_1 @
% 0.38/0.58             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X28 @ X29)
% 0.38/0.58          | (m1_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.38/0.58          | ~ (l1_pre_topc @ X29))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.38/0.58        | (m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf(t5_connsp_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.38/0.58                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.58          | ~ (v3_pre_topc @ X19 @ X20)
% 0.38/0.58          | ~ (r2_hidden @ X21 @ X19)
% 0.38/0.58          | (m1_connsp_2 @ X19 @ X20 @ X21)
% 0.38/0.58          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.38/0.58          | ~ (l1_pre_topc @ X20)
% 0.38/0.58          | ~ (v2_pre_topc @ X20)
% 0.38/0.58          | (v2_struct_0 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.58  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf(t16_tsep_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.38/0.58                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X25 @ X26)
% 0.38/0.58          | ((X27) != (u1_struct_0 @ X25))
% 0.38/0.58          | ~ (v1_tsep_1 @ X25 @ X26)
% 0.38/0.58          | ~ (m1_pre_topc @ X25 @ X26)
% 0.38/0.58          | (v3_pre_topc @ X27 @ X26)
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.58          | ~ (l1_pre_topc @ X26)
% 0.38/0.58          | ~ (v2_pre_topc @ X26))),
% 0.38/0.58      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i]:
% 0.38/0.58         (~ (v2_pre_topc @ X26)
% 0.38/0.58          | ~ (l1_pre_topc @ X26)
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.58          | (v3_pre_topc @ (u1_struct_0 @ X25) @ X26)
% 0.38/0.58          | ~ (v1_tsep_1 @ X25 @ X26)
% 0.38/0.58          | ~ (m1_pre_topc @ X25 @ X26))),
% 0.38/0.58      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      ((~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.58        | ~ (v1_tsep_1 @ sk_D_1 @ sk_B)
% 0.38/0.58        | (v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['33', '35'])).
% 0.38/0.58  thf('37', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('38', plain, ((v1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('41', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D_1) @ sk_B)),
% 0.38/0.58      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['30', '31', '32', '41'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['23', '42'])).
% 0.38/0.58  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (((m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E)
% 0.38/0.58        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '45'])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf(t7_connsp_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.38/0.58                    ( ![D:$i]:
% 0.38/0.58                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.38/0.58                          ( m1_subset_1 @
% 0.38/0.58                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.58                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.38/0.58                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.38/0.58          | (m1_connsp_2 @ (sk_D @ X24 @ X22 @ X23) @ X23 @ X22)
% 0.38/0.58          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.38/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.58          | ~ (l1_pre_topc @ X23)
% 0.38/0.58          | ~ (v2_pre_topc @ X23)
% 0.38/0.58          | (v2_struct_0 @ X23))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.38/0.58             sk_B @ X0)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.58  thf('50', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.38/0.58             sk_B @ X0)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58           sk_B @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['46', '52'])).
% 0.38/0.58  thf('54', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58           sk_B @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.58  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (((m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ sk_B @ 
% 0.38/0.58         sk_E)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '45'])).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.38/0.58          | (r1_tarski @ (sk_D @ X24 @ X22 @ X23) @ X24)
% 0.38/0.58          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.38/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.58          | ~ (l1_pre_topc @ X23)
% 0.38/0.58          | ~ (v2_pre_topc @ X23)
% 0.38/0.58          | (v2_struct_0 @ X23))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.38/0.58             (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.58  thf('62', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.38/0.58             (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58           (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['58', '64'])).
% 0.38/0.58  thf('66', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58           (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.58  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58         (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['67', '68'])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ sk_E))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '45'])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.38/0.58          | (m1_subset_1 @ (sk_D @ X24 @ X22 @ X23) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.58          | ~ (m1_connsp_2 @ X24 @ X23 @ X22)
% 0.38/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.38/0.58          | ~ (l1_pre_topc @ X23)
% 0.38/0.58          | ~ (v2_pre_topc @ X23)
% 0.38/0.58          | (v2_struct_0 @ X23))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_connsp_2])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.58  thf('74', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D_1) @ sk_B @ X0)
% 0.38/0.58          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ X0 @ sk_B) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.38/0.58  thf('77', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['70', '76'])).
% 0.38/0.58  thf('78', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.38/0.58  thf('80', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('81', plain,
% 0.38/0.58      (((m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['79', '80'])).
% 0.38/0.58  thf('82', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)
% 0.38/0.58        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.38/0.58      inference('split', [status(esa)], ['82'])).
% 0.38/0.58  thf('84', plain, (((sk_E) = (sk_F))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['83', '84'])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)
% 0.38/0.58        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('87', plain,
% 0.38/0.58      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.38/0.58       ~
% 0.38/0.58       ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))),
% 0.38/0.58      inference('split', [status(esa)], ['86'])).
% 0.38/0.58  thf('88', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('89', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('split', [status(esa)], ['82'])).
% 0.38/0.58  thf('90', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t64_tmap_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                 ( m1_subset_1 @
% 0.38/0.58                   C @ 
% 0.38/0.58                   ( k1_zfmisc_1 @
% 0.38/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                       ( ![F:$i]:
% 0.38/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.58                           ( ( ( ( E ) = ( F ) ) & 
% 0.38/0.58                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.38/0.58                             ( r1_tmap_1 @
% 0.38/0.58                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X31)
% 0.38/0.58          | ~ (m1_pre_topc @ X31 @ X30)
% 0.38/0.58          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.38/0.58          | (r1_tmap_1 @ X31 @ X33 @ (k2_tmap_1 @ X30 @ X33 @ X34 @ X31) @ X32)
% 0.38/0.58          | ((X35) != (X32))
% 0.38/0.58          | ~ (r1_tmap_1 @ X30 @ X33 @ X34 @ X35)
% 0.38/0.58          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X30))
% 0.38/0.58          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))))
% 0.38/0.58          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))
% 0.38/0.58          | ~ (v1_funct_1 @ X34)
% 0.38/0.58          | ~ (l1_pre_topc @ X33)
% 0.38/0.58          | ~ (v2_pre_topc @ X33)
% 0.38/0.58          | (v2_struct_0 @ X33))),
% 0.38/0.58      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.38/0.58  thf('92', plain,
% 0.38/0.58      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X33)
% 0.38/0.58          | ~ (v2_pre_topc @ X33)
% 0.38/0.58          | ~ (l1_pre_topc @ X33)
% 0.38/0.58          | ~ (v1_funct_1 @ X34)
% 0.38/0.58          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))
% 0.38/0.58          | ~ (m1_subset_1 @ X34 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X33))))
% 0.38/0.58          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.38/0.58          | ~ (r1_tmap_1 @ X30 @ X33 @ X34 @ X32)
% 0.38/0.58          | (r1_tmap_1 @ X31 @ X33 @ (k2_tmap_1 @ X30 @ X33 @ X34 @ X31) @ X32)
% 0.38/0.58          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.38/0.58          | ~ (m1_pre_topc @ X31 @ X30)
% 0.38/0.58          | (v2_struct_0 @ X31)
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X30))),
% 0.38/0.58      inference('simplify', [status(thm)], ['91'])).
% 0.38/0.58  thf('93', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.58          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.38/0.58          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['90', '92'])).
% 0.38/0.58  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('96', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.58          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.38/0.58          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['93', '94', '95', '96', '97', '98', '99'])).
% 0.38/0.58  thf('101', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          ((v2_struct_0 @ sk_A)
% 0.38/0.58           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.58           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.38/0.58              sk_E)
% 0.38/0.58           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.38/0.58           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.58           | (v2_struct_0 @ X0)
% 0.38/0.58           | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['89', '100'])).
% 0.38/0.58  thf('102', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('103', plain,
% 0.38/0.58      ((![X0 : $i]:
% 0.38/0.58          ((v2_struct_0 @ sk_A)
% 0.38/0.58           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.38/0.58              sk_E)
% 0.38/0.58           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.38/0.58           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.58           | (v2_struct_0 @ X0)
% 0.38/0.58           | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('demod', [status(thm)], ['101', '102'])).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_B)
% 0.38/0.58         | (v2_struct_0 @ sk_D_1)
% 0.38/0.58         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.58         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)
% 0.38/0.58         | (v2_struct_0 @ sk_A)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['88', '103'])).
% 0.38/0.58  thf('105', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('106', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_B)
% 0.38/0.58         | (v2_struct_0 @ sk_D_1)
% 0.38/0.58         | (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)
% 0.38/0.58         | (v2_struct_0 @ sk_A)))
% 0.38/0.58         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('demod', [status(thm)], ['104', '105'])).
% 0.38/0.58  thf('107', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.38/0.58      inference('split', [status(esa)], ['86'])).
% 0.38/0.58  thf('108', plain, (((sk_E) = (sk_F))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('109', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['107', '108'])).
% 0.38/0.58  thf('110', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.38/0.58             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['106', '109'])).
% 0.38/0.58  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('112', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.38/0.58             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('clc', [status(thm)], ['110', '111'])).
% 0.38/0.58  thf('113', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('114', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_D_1))
% 0.38/0.58         <= (~
% 0.38/0.58             ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) & 
% 0.38/0.58             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('clc', [status(thm)], ['112', '113'])).
% 0.38/0.58  thf('115', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('116', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) | 
% 0.38/0.58       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.38/0.58      inference('sup-', [status(thm)], ['114', '115'])).
% 0.38/0.58  thf('117', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F)) | 
% 0.38/0.58       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.38/0.58      inference('split', [status(esa)], ['82'])).
% 0.38/0.58  thf('118', plain,
% 0.38/0.58      (((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58         (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_F))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['87', '116', '117'])).
% 0.38/0.58  thf('119', plain,
% 0.38/0.58      ((r1_tmap_1 @ sk_D_1 @ sk_A @ 
% 0.38/0.58        (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1) @ sk_E)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['85', '118'])).
% 0.38/0.58  thf('120', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t65_tmap_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                 ( m1_subset_1 @
% 0.38/0.58                   C @ 
% 0.38/0.58                   ( k1_zfmisc_1 @
% 0.38/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( m1_subset_1 @
% 0.38/0.58                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.58                       ( ![F:$i]:
% 0.38/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                           ( ![G:$i]:
% 0.38/0.58                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.38/0.58                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.38/0.58                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.38/0.58                                   ( ( F ) = ( G ) ) ) =>
% 0.38/0.58                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.38/0.58                                   ( r1_tmap_1 @
% 0.38/0.58                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('121', plain,
% 0.38/0.58      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X36)
% 0.38/0.58          | ~ (v2_pre_topc @ X36)
% 0.38/0.58          | ~ (l1_pre_topc @ X36)
% 0.38/0.58          | (v2_struct_0 @ X37)
% 0.38/0.58          | ~ (m1_pre_topc @ X37 @ X36)
% 0.38/0.58          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.38/0.58          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X37))
% 0.38/0.58          | ~ (m1_connsp_2 @ X39 @ X36 @ X38)
% 0.38/0.58          | ((X38) != (X40))
% 0.38/0.58          | ~ (r1_tmap_1 @ X37 @ X41 @ (k2_tmap_1 @ X36 @ X41 @ X42 @ X37) @ 
% 0.38/0.58               X40)
% 0.38/0.58          | (r1_tmap_1 @ X36 @ X41 @ X42 @ X38)
% 0.38/0.58          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.38/0.58          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.38/0.58          | ~ (m1_subset_1 @ X42 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))))
% 0.38/0.58          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))
% 0.38/0.58          | ~ (v1_funct_1 @ X42)
% 0.38/0.58          | ~ (l1_pre_topc @ X41)
% 0.38/0.58          | ~ (v2_pre_topc @ X41)
% 0.38/0.58          | (v2_struct_0 @ X41))),
% 0.38/0.58      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.38/0.58  thf('122', plain,
% 0.38/0.58      (![X36 : $i, X37 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X41)
% 0.38/0.58          | ~ (v2_pre_topc @ X41)
% 0.38/0.58          | ~ (l1_pre_topc @ X41)
% 0.38/0.58          | ~ (v1_funct_1 @ X42)
% 0.38/0.58          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))
% 0.38/0.58          | ~ (m1_subset_1 @ X42 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X41))))
% 0.38/0.58          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.38/0.58          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.38/0.58          | (r1_tmap_1 @ X36 @ X41 @ X42 @ X40)
% 0.38/0.58          | ~ (r1_tmap_1 @ X37 @ X41 @ (k2_tmap_1 @ X36 @ X41 @ X42 @ X37) @ 
% 0.38/0.58               X40)
% 0.38/0.58          | ~ (m1_connsp_2 @ X39 @ X36 @ X40)
% 0.38/0.58          | ~ (r1_tarski @ X39 @ (u1_struct_0 @ X37))
% 0.38/0.58          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X36))
% 0.38/0.58          | ~ (m1_pre_topc @ X37 @ X36)
% 0.38/0.58          | (v2_struct_0 @ X37)
% 0.38/0.58          | ~ (l1_pre_topc @ X36)
% 0.38/0.58          | ~ (v2_pre_topc @ X36)
% 0.38/0.58          | (v2_struct_0 @ X36))),
% 0.38/0.58      inference('simplify', [status(thm)], ['121'])).
% 0.38/0.58  thf('123', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.38/0.58          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.38/0.58               X1)
% 0.38/0.58          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['120', '122'])).
% 0.38/0.58  thf('124', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('125', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('126', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('130', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (m1_connsp_2 @ X2 @ sk_B @ X1)
% 0.38/0.58          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.38/0.58               X1)
% 0.38/0.58          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['123', '124', '125', '126', '127', '128', '129'])).
% 0.38/0.58  thf('131', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.38/0.58          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.38/0.58          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['119', '130'])).
% 0.38/0.58  thf('132', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('133', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('134', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('135', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.38/0.58          | ~ (m1_connsp_2 @ X0 @ sk_B @ sk_E)
% 0.38/0.58          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 0.38/0.58  thf('136', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | ~ (r1_tarski @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58             (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58             sk_B @ sk_E)
% 0.38/0.58        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['81', '135'])).
% 0.38/0.58  thf('137', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.38/0.58        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58             sk_B @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['69', '136'])).
% 0.38/0.58  thf('138', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | ~ (m1_connsp_2 @ (sk_D @ (u1_struct_0 @ sk_D_1) @ sk_E @ sk_B) @ 
% 0.38/0.58             sk_B @ sk_E)
% 0.38/0.58        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['137'])).
% 0.38/0.58  thf('139', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['57', '138'])).
% 0.38/0.58  thf('140', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['139'])).
% 0.38/0.58  thf('141', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.38/0.58         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.38/0.58      inference('split', [status(esa)], ['86'])).
% 0.38/0.58  thf('142', plain, (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['87', '116'])).
% 0.38/0.58  thf('143', plain, (~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['141', '142'])).
% 0.38/0.58  thf('144', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['140', '143'])).
% 0.38/0.58  thf('145', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf(dt_k1_connsp_2, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58       ( m1_subset_1 @
% 0.38/0.58         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.58  thf('146', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ X12)
% 0.38/0.58          | ~ (v2_pre_topc @ X12)
% 0.38/0.58          | (v2_struct_0 @ X12)
% 0.38/0.58          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.38/0.58          | (m1_subset_1 @ (k1_connsp_2 @ X12 @ X13) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.38/0.58  thf('147', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58        | (v2_struct_0 @ sk_D_1)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_D_1)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_D_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['145', '146'])).
% 0.38/0.58  thf('148', plain, ((v2_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.38/0.58  thf('149', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('150', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.58        | (v2_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.38/0.58  thf('151', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('152', plain,
% 0.38/0.58      ((m1_subset_1 @ (k1_connsp_2 @ sk_D_1 @ sk_E) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['150', '151'])).
% 0.38/0.58  thf(t5_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.58          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.58  thf('153', plain,
% 0.38/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X2 @ X3)
% 0.38/0.58          | ~ (v1_xboole_0 @ X4)
% 0.38/0.58          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.58  thf('154', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['152', '153'])).
% 0.38/0.58  thf('155', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_D_1)
% 0.38/0.58          | (v2_struct_0 @ sk_A)
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D_1 @ sk_E)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['144', '154'])).
% 0.38/0.58  thf('156', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['19', '155'])).
% 0.38/0.58  thf('157', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('158', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1))),
% 0.38/0.58      inference('clc', [status(thm)], ['156', '157'])).
% 0.38/0.58  thf('159', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('160', plain, ((v2_struct_0 @ sk_D_1)),
% 0.38/0.58      inference('clc', [status(thm)], ['158', '159'])).
% 0.38/0.58  thf('161', plain, ($false), inference('demod', [status(thm)], ['0', '160'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
