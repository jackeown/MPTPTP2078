%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IYHWBbJ8XB

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:53 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 407 expanded)
%              Number of leaves         :   38 ( 128 expanded)
%              Depth                    :   25
%              Number of atoms          : 1825 (12974 expanded)
%              Number of equality atoms :   13 ( 191 expanded)
%              Maximal formula depth    :   28 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( r2_hidden @ X26 @ ( k1_connsp_2 @ X27 @ X26 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['5','11','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_E @ ( k1_connsp_2 @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( m1_connsp_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
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

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( X33
       != ( u1_struct_0 @ X31 ) )
      | ~ ( v1_tsep_1 @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v3_pre_topc @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('36',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X31 ) @ X32 )
      | ~ ( v1_tsep_1 @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B_1 )
    | ~ ( v1_tsep_1 @ sk_D @ sk_B_1 )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_tsep_1 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['33','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['22','46'])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('49',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('56',plain,
    ( ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['49'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ( r1_tmap_1 @ X37 @ X39 @ ( k2_tmap_1 @ X36 @ X39 @ X40 @ X37 ) @ X38 )
      | ( X41 != X38 )
      | ~ ( r1_tmap_1 @ X36 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('59',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tmap_1 @ X36 @ X39 @ X40 @ X38 )
      | ( r1_tmap_1 @ X37 @ X39 @ ( k2_tmap_1 @ X36 @ X39 @ X40 @ X37 ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B_1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['55','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['53'])).

thf('75',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['49'])).

thf('85',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['54','83','84'])).

thf('86',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ sk_E ),
    inference(simpl_trail,[status(thm)],['52','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('88',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ( v2_struct_0 @ X43 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X42 ) )
      | ~ ( r1_tarski @ X45 @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_connsp_2 @ X45 @ X42 @ X44 )
      | ( X44 != X46 )
      | ~ ( r1_tmap_1 @ X43 @ X47 @ ( k2_tmap_1 @ X42 @ X47 @ X48 @ X43 ) @ X46 )
      | ( r1_tmap_1 @ X42 @ X47 @ X48 @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X47 ) ) ) )
      | ~ ( v1_funct_2 @ X48 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X47 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_tmap_1])).

thf('89',plain,(
    ! [X42: $i,X43: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X47 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X47 ) ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X43 ) )
      | ( r1_tmap_1 @ X42 @ X47 @ X48 @ X46 )
      | ~ ( r1_tmap_1 @ X43 @ X47 @ ( k2_tmap_1 @ X42 @ X47 @ X48 @ X43 ) @ X46 )
      | ~ ( m1_connsp_2 @ X45 @ X42 @ X46 )
      | ~ ( r1_tarski @ X45 @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_connsp_2 @ X2 @ sk_B_1 @ X1 )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_B_1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['86','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('100',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
      | ~ ( m1_connsp_2 @ X0 @ sk_B_1 @ sk_E )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','102'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_D ) @ sk_B_1 @ sk_E )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','106'])).

thf('108',plain,
    ( ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['53'])).

thf('109',plain,(
    ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['54','83'])).

thf('110',plain,(
    ~ ( r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('114',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v2_pre_topc @ sk_D )
    | ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('116',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('120',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['111','121'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['0','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IYHWBbJ8XB
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:07:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 289 iterations in 0.179s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.59  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.41/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.59  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.41/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.59  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.41/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.59  thf(t67_tmap_1, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.59             ( l1_pre_topc @ B ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.59                 ( m1_subset_1 @
% 0.41/0.59                   C @ 
% 0.41/0.59                   ( k1_zfmisc_1 @
% 0.41/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.59               ( ![D:$i]:
% 0.41/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.41/0.59                     ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.59                   ( ![E:$i]:
% 0.41/0.59                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.59                       ( ![F:$i]:
% 0.41/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.59                           ( ( ( E ) = ( F ) ) =>
% 0.41/0.59                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.41/0.59                               ( r1_tmap_1 @
% 0.41/0.59                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.59            ( l1_pre_topc @ A ) ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.59                ( l1_pre_topc @ B ) ) =>
% 0.41/0.59              ( ![C:$i]:
% 0.41/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.59                    ( v1_funct_2 @
% 0.41/0.59                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.59                    ( m1_subset_1 @
% 0.41/0.59                      C @ 
% 0.41/0.59                      ( k1_zfmisc_1 @
% 0.41/0.59                        ( k2_zfmisc_1 @
% 0.41/0.59                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.59                  ( ![D:$i]:
% 0.41/0.59                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.41/0.59                        ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.59                      ( ![E:$i]:
% 0.41/0.59                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.59                          ( ![F:$i]:
% 0.41/0.59                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.59                              ( ( ( E ) = ( F ) ) =>
% 0.41/0.59                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.41/0.59                                  ( r1_tmap_1 @
% 0.41/0.59                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.41/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('2', plain, (((sk_E) = (sk_F))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf(t30_connsp_2, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.59           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X26 : $i, X27 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.41/0.59          | (r2_hidden @ X26 @ (k1_connsp_2 @ X27 @ X26))
% 0.41/0.59          | ~ (l1_pre_topc @ X27)
% 0.41/0.59          | ~ (v2_pre_topc @ X27)
% 0.41/0.59          | (v2_struct_0 @ X27))),
% 0.41/0.59      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_D)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_D)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_D)
% 0.41/0.59        | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D @ sk_E)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc1_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X14 @ X15)
% 0.41/0.59          | (v2_pre_topc @ X14)
% 0.41/0.59          | ~ (l1_pre_topc @ X15)
% 0.41/0.59          | ~ (v2_pre_topc @ X15))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      ((~ (v2_pre_topc @ sk_B_1)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.59        | (v2_pre_topc @ sk_D))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf('9', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('10', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('11', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.59  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(dt_m1_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X16 : $i, X17 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X16 @ X17)
% 0.41/0.59          | (l1_pre_topc @ X16)
% 0.41/0.59          | ~ (l1_pre_topc @ X17))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.59  thf('14', plain, ((~ (l1_pre_topc @ sk_B_1) | (l1_pre_topc @ sk_D))),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('15', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_D) | (r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D @ sk_E)))),
% 0.41/0.59      inference('demod', [status(thm)], ['5', '11', '16'])).
% 0.41/0.59  thf('18', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('19', plain, ((r2_hidden @ sk_E @ (k1_connsp_2 @ sk_D @ sk_E))),
% 0.41/0.59      inference('clc', [status(thm)], ['17', '18'])).
% 0.41/0.59  thf('20', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf(t2_subset, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         ((r2_hidden @ X6 @ X7)
% 0.41/0.59          | (v1_xboole_0 @ X7)
% 0.41/0.59          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.59  thf('23', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t1_tsep_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.59           ( m1_subset_1 @
% 0.41/0.59             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X34 : $i, X35 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X34 @ X35)
% 0.41/0.59          | (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.41/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.41/0.59          | ~ (l1_pre_topc @ X35))),
% 0.41/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_B_1)
% 0.41/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('27', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf(t5_connsp_2, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.59               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.41/0.59                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.41/0.59          | ~ (v3_pre_topc @ X28 @ X29)
% 0.41/0.59          | ~ (r2_hidden @ X30 @ X28)
% 0.41/0.59          | (m1_connsp_2 @ X28 @ X29 @ X30)
% 0.41/0.59          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.41/0.59          | ~ (l1_pre_topc @ X29)
% 0.41/0.59          | ~ (v2_pre_topc @ X29)
% 0.41/0.59          | (v2_struct_0 @ X29))),
% 0.41/0.59      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_B_1)
% 0.41/0.59          | ~ (v2_pre_topc @ sk_B_1)
% 0.41/0.59          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ X0)
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('32', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_B_1)
% 0.41/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ X0)
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59          | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf(t16_tsep_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.41/0.59                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.41/0.59                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X31 @ X32)
% 0.41/0.59          | ((X33) != (u1_struct_0 @ X31))
% 0.41/0.59          | ~ (v1_tsep_1 @ X31 @ X32)
% 0.41/0.59          | ~ (m1_pre_topc @ X31 @ X32)
% 0.41/0.59          | (v3_pre_topc @ X33 @ X32)
% 0.41/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.41/0.59          | ~ (l1_pre_topc @ X32)
% 0.41/0.59          | ~ (v2_pre_topc @ X32))),
% 0.41/0.59      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X31 : $i, X32 : $i]:
% 0.41/0.59         (~ (v2_pre_topc @ X32)
% 0.41/0.59          | ~ (l1_pre_topc @ X32)
% 0.41/0.59          | ~ (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.41/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.41/0.59          | (v3_pre_topc @ (u1_struct_0 @ X31) @ X32)
% 0.41/0.59          | ~ (v1_tsep_1 @ X31 @ X32)
% 0.41/0.59          | ~ (m1_pre_topc @ X31 @ X32))),
% 0.41/0.59      inference('simplify', [status(thm)], ['35'])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      ((~ (m1_pre_topc @ sk_D @ sk_B_1)
% 0.41/0.59        | ~ (v1_tsep_1 @ sk_D @ sk_B_1)
% 0.41/0.59        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['34', '36'])).
% 0.41/0.59  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('39', plain, ((v1_tsep_1 @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('40', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('41', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('42', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_B_1)
% 0.41/0.59          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ X0)
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_D)))),
% 0.41/0.59      inference('demod', [status(thm)], ['33', '42'])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.41/0.59        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.41/0.59        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['23', '43'])).
% 0.41/0.59  thf('45', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      (((m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.41/0.59        | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.41/0.59      inference('clc', [status(thm)], ['44', '45'])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59        | (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E))),
% 0.41/0.59      inference('sup-', [status(thm)], ['22', '46'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['26', '27'])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59         sk_F)
% 0.41/0.59        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59         sk_F))
% 0.41/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.41/0.59      inference('split', [status(esa)], ['49'])).
% 0.41/0.59  thf('51', plain, (((sk_E) = (sk_F))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59         sk_E))
% 0.41/0.59         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.41/0.59      inference('demod', [status(thm)], ['50', '51'])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)
% 0.41/0.59        | ~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)) | 
% 0.41/0.59       ~
% 0.41/0.59       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59         sk_F))),
% 0.41/0.59      inference('split', [status(esa)], ['53'])).
% 0.41/0.59  thf('55', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))
% 0.41/0.59         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('split', [status(esa)], ['49'])).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t64_tmap_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.59             ( l1_pre_topc @ B ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.59                 ( m1_subset_1 @
% 0.41/0.59                   C @ 
% 0.41/0.59                   ( k1_zfmisc_1 @
% 0.41/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.59               ( ![D:$i]:
% 0.41/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.59                   ( ![E:$i]:
% 0.41/0.59                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.59                       ( ![F:$i]:
% 0.41/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.59                           ( ( ( ( E ) = ( F ) ) & 
% 0.41/0.59                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.41/0.59                             ( r1_tmap_1 @
% 0.41/0.59                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.41/0.59         ((v2_struct_0 @ X36)
% 0.41/0.59          | ~ (v2_pre_topc @ X36)
% 0.41/0.59          | ~ (l1_pre_topc @ X36)
% 0.41/0.59          | (v2_struct_0 @ X37)
% 0.41/0.59          | ~ (m1_pre_topc @ X37 @ X36)
% 0.41/0.59          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 0.41/0.59          | (r1_tmap_1 @ X37 @ X39 @ (k2_tmap_1 @ X36 @ X39 @ X40 @ X37) @ X38)
% 0.41/0.59          | ((X41) != (X38))
% 0.41/0.59          | ~ (r1_tmap_1 @ X36 @ X39 @ X40 @ X41)
% 0.41/0.59          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X36))
% 0.41/0.59          | ~ (m1_subset_1 @ X40 @ 
% 0.41/0.59               (k1_zfmisc_1 @ 
% 0.41/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))))
% 0.41/0.59          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))
% 0.41/0.59          | ~ (v1_funct_1 @ X40)
% 0.41/0.59          | ~ (l1_pre_topc @ X39)
% 0.41/0.59          | ~ (v2_pre_topc @ X39)
% 0.41/0.59          | (v2_struct_0 @ X39))),
% 0.41/0.59      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.41/0.59         ((v2_struct_0 @ X39)
% 0.41/0.59          | ~ (v2_pre_topc @ X39)
% 0.41/0.59          | ~ (l1_pre_topc @ X39)
% 0.41/0.59          | ~ (v1_funct_1 @ X40)
% 0.41/0.59          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))
% 0.41/0.59          | ~ (m1_subset_1 @ X40 @ 
% 0.41/0.59               (k1_zfmisc_1 @ 
% 0.41/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))))
% 0.41/0.59          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.41/0.59          | ~ (r1_tmap_1 @ X36 @ X39 @ X40 @ X38)
% 0.41/0.59          | (r1_tmap_1 @ X37 @ X39 @ (k2_tmap_1 @ X36 @ X39 @ X40 @ X37) @ X38)
% 0.41/0.59          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 0.41/0.59          | ~ (m1_pre_topc @ X37 @ X36)
% 0.41/0.59          | (v2_struct_0 @ X37)
% 0.41/0.59          | ~ (l1_pre_topc @ X36)
% 0.41/0.59          | ~ (v2_pre_topc @ X36)
% 0.41/0.59          | (v2_struct_0 @ X36))),
% 0.41/0.59      inference('simplify', [status(thm)], ['58'])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_B_1)
% 0.41/0.59          | ~ (v2_pre_topc @ sk_B_1)
% 0.41/0.59          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.59          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.41/0.59             X1)
% 0.41/0.59          | ~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.59               (u1_struct_0 @ sk_A))
% 0.41/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59          | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['57', '59'])).
% 0.41/0.59  thf('61', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('62', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('63', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('67', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_B_1)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.59          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.41/0.59             X1)
% 0.41/0.59          | ~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)],
% 0.41/0.59                ['60', '61', '62', '63', '64', '65', '66'])).
% 0.41/0.59  thf('68', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          ((v2_struct_0 @ sk_A)
% 0.41/0.59           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.59              (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ sk_E)
% 0.41/0.59           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.41/0.59           | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.59           | (v2_struct_0 @ X0)
% 0.41/0.59           | (v2_struct_0 @ sk_B_1)))
% 0.41/0.59         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['56', '67'])).
% 0.41/0.59  thf('69', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('70', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          ((v2_struct_0 @ sk_A)
% 0.41/0.59           | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.59              (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ sk_E)
% 0.41/0.59           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.41/0.59           | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.59           | (v2_struct_0 @ X0)
% 0.41/0.59           | (v2_struct_0 @ sk_B_1)))
% 0.41/0.59         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('demod', [status(thm)], ['68', '69'])).
% 0.41/0.59  thf('71', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_B_1)
% 0.41/0.59         | (v2_struct_0 @ sk_D)
% 0.41/0.59         | ~ (m1_pre_topc @ sk_D @ sk_B_1)
% 0.41/0.59         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59            (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.41/0.59         | (v2_struct_0 @ sk_A)))
% 0.41/0.59         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['55', '70'])).
% 0.41/0.59  thf('72', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('73', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_B_1)
% 0.41/0.59         | (v2_struct_0 @ sk_D)
% 0.41/0.59         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59            (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.41/0.59         | (v2_struct_0 @ sk_A)))
% 0.41/0.59         <= (((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('demod', [status(thm)], ['71', '72'])).
% 0.41/0.59  thf('74', plain,
% 0.41/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F))
% 0.41/0.59         <= (~
% 0.41/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.41/0.59      inference('split', [status(esa)], ['53'])).
% 0.41/0.59  thf('75', plain, (((sk_E) = (sk_F))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('76', plain,
% 0.41/0.59      ((~ (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_E))
% 0.41/0.59         <= (~
% 0.41/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.41/0.59      inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.59  thf('77', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B_1)))
% 0.41/0.59         <= (~
% 0.41/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.41/0.59             ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['73', '76'])).
% 0.41/0.59  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('79', plain,
% 0.41/0.59      ((((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_D)))
% 0.41/0.59         <= (~
% 0.41/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.41/0.59             ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('clc', [status(thm)], ['77', '78'])).
% 0.41/0.59  thf('80', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('81', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_D))
% 0.41/0.59         <= (~
% 0.41/0.59             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.41/0.59             ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('clc', [status(thm)], ['79', '80'])).
% 0.41/0.59  thf('82', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('83', plain,
% 0.41/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59         sk_F)) | 
% 0.41/0.59       ~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.41/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.41/0.59  thf('84', plain,
% 0.41/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59         sk_F)) | 
% 0.41/0.59       ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.41/0.59      inference('split', [status(esa)], ['49'])).
% 0.41/0.59  thf('85', plain,
% 0.41/0.59      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59         sk_F))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['54', '83', '84'])).
% 0.41/0.59  thf('86', plain,
% 0.41/0.59      ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.41/0.59        sk_E)),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['52', '85'])).
% 0.41/0.59  thf('87', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ 
% 0.41/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t65_tmap_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.59             ( l1_pre_topc @ B ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.59                 ( m1_subset_1 @
% 0.41/0.59                   C @ 
% 0.41/0.59                   ( k1_zfmisc_1 @
% 0.41/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.59               ( ![D:$i]:
% 0.41/0.59                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.41/0.59                   ( ![E:$i]:
% 0.41/0.59                     ( ( m1_subset_1 @
% 0.41/0.59                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.59                       ( ![F:$i]:
% 0.41/0.59                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.41/0.59                           ( ![G:$i]:
% 0.41/0.59                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.41/0.59                               ( ( ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.41/0.59                                   ( m1_connsp_2 @ E @ B @ F ) & 
% 0.41/0.59                                   ( ( F ) = ( G ) ) ) =>
% 0.41/0.59                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.41/0.59                                   ( r1_tmap_1 @
% 0.41/0.59                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('88', plain,
% 0.41/0.59      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.41/0.59         ((v2_struct_0 @ X42)
% 0.41/0.59          | ~ (v2_pre_topc @ X42)
% 0.41/0.59          | ~ (l1_pre_topc @ X42)
% 0.41/0.59          | (v2_struct_0 @ X43)
% 0.41/0.59          | ~ (m1_pre_topc @ X43 @ X42)
% 0.41/0.59          | ~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X42))
% 0.41/0.59          | ~ (r1_tarski @ X45 @ (u1_struct_0 @ X43))
% 0.41/0.59          | ~ (m1_connsp_2 @ X45 @ X42 @ X44)
% 0.41/0.59          | ((X44) != (X46))
% 0.41/0.59          | ~ (r1_tmap_1 @ X43 @ X47 @ (k2_tmap_1 @ X42 @ X47 @ X48 @ X43) @ 
% 0.41/0.59               X46)
% 0.41/0.59          | (r1_tmap_1 @ X42 @ X47 @ X48 @ X44)
% 0.41/0.59          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X43))
% 0.41/0.59          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.41/0.59          | ~ (m1_subset_1 @ X48 @ 
% 0.41/0.59               (k1_zfmisc_1 @ 
% 0.41/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X47))))
% 0.41/0.59          | ~ (v1_funct_2 @ X48 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X47))
% 0.41/0.59          | ~ (v1_funct_1 @ X48)
% 0.41/0.59          | ~ (l1_pre_topc @ X47)
% 0.41/0.59          | ~ (v2_pre_topc @ X47)
% 0.41/0.59          | (v2_struct_0 @ X47))),
% 0.41/0.59      inference('cnf', [status(esa)], [t65_tmap_1])).
% 0.41/0.59  thf('89', plain,
% 0.41/0.59      (![X42 : $i, X43 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.41/0.59         ((v2_struct_0 @ X47)
% 0.41/0.59          | ~ (v2_pre_topc @ X47)
% 0.41/0.59          | ~ (l1_pre_topc @ X47)
% 0.41/0.59          | ~ (v1_funct_1 @ X48)
% 0.41/0.59          | ~ (v1_funct_2 @ X48 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X47))
% 0.41/0.59          | ~ (m1_subset_1 @ X48 @ 
% 0.41/0.59               (k1_zfmisc_1 @ 
% 0.41/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X47))))
% 0.41/0.59          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.41/0.59          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X43))
% 0.41/0.59          | (r1_tmap_1 @ X42 @ X47 @ X48 @ X46)
% 0.41/0.59          | ~ (r1_tmap_1 @ X43 @ X47 @ (k2_tmap_1 @ X42 @ X47 @ X48 @ X43) @ 
% 0.41/0.59               X46)
% 0.41/0.59          | ~ (m1_connsp_2 @ X45 @ X42 @ X46)
% 0.41/0.59          | ~ (r1_tarski @ X45 @ (u1_struct_0 @ X43))
% 0.41/0.59          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X42))
% 0.41/0.59          | ~ (m1_pre_topc @ X43 @ X42)
% 0.41/0.59          | (v2_struct_0 @ X43)
% 0.41/0.59          | ~ (l1_pre_topc @ X42)
% 0.41/0.59          | ~ (v2_pre_topc @ X42)
% 0.41/0.59          | (v2_struct_0 @ X42))),
% 0.41/0.59      inference('simplify', [status(thm)], ['88'])).
% 0.41/0.59  thf('90', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_B_1)
% 0.41/0.59          | ~ (v2_pre_topc @ sk_B_1)
% 0.41/0.59          | ~ (l1_pre_topc @ sk_B_1)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B_1 @ X1)
% 0.41/0.59          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.41/0.59          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.59          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 0.41/0.59               (u1_struct_0 @ sk_A))
% 0.41/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.59          | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['87', '89'])).
% 0.41/0.59  thf('91', plain, ((v2_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('92', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('93', plain,
% 0.41/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('97', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_B_1)
% 0.41/0.59          | (v2_struct_0 @ X0)
% 0.41/0.59          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.41/0.59          | ~ (m1_connsp_2 @ X2 @ sk_B_1 @ X1)
% 0.41/0.59          | ~ (r1_tmap_1 @ X0 @ sk_A @ 
% 0.41/0.59               (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.41/0.59          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X1)
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.41/0.59          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.59          | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)],
% 0.41/0.59                ['90', '91', '92', '93', '94', '95', '96'])).
% 0.41/0.59  thf('98', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_A)
% 0.41/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.59          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))
% 0.41/0.59          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.41/0.59          | ~ (m1_connsp_2 @ X0 @ sk_B_1 @ sk_E)
% 0.41/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59          | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))
% 0.41/0.59          | ~ (m1_pre_topc @ sk_D @ sk_B_1)
% 0.41/0.59          | (v2_struct_0 @ sk_D)
% 0.41/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['86', '97'])).
% 0.41/0.59  thf('99', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf('100', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B_1))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('102', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_A)
% 0.41/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.41/0.59          | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.41/0.59          | ~ (m1_connsp_2 @ X0 @ sk_B_1 @ sk_E)
% 0.41/0.59          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59          | (v2_struct_0 @ sk_D)
% 0.41/0.59          | (v2_struct_0 @ sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.41/0.59  thf('103', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_B_1)
% 0.41/0.59        | (v2_struct_0 @ sk_D)
% 0.41/0.59        | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.41/0.59        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.41/0.59        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.41/0.59        | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['48', '102'])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('104', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('105', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.41/0.59      inference('simplify', [status(thm)], ['104'])).
% 0.41/0.59  thf('106', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_B_1)
% 0.41/0.59        | (v2_struct_0 @ sk_D)
% 0.41/0.59        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_D) @ sk_B_1 @ sk_E)
% 0.41/0.59        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.41/0.59        | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['103', '105'])).
% 0.41/0.59  thf('107', plain,
% 0.41/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59        | (v2_struct_0 @ sk_A)
% 0.41/0.59        | (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)
% 0.41/0.59        | (v2_struct_0 @ sk_D)
% 0.41/0.59        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['47', '106'])).
% 0.41/0.59  thf('108', plain,
% 0.41/0.59      ((~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))
% 0.41/0.59         <= (~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)))),
% 0.41/0.59      inference('split', [status(esa)], ['53'])).
% 0.41/0.59  thf('109', plain, (~ ((r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['54', '83'])).
% 0.41/0.59  thf('110', plain, (~ (r1_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_E)),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['108', '109'])).
% 0.41/0.59  thf('111', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_B_1)
% 0.41/0.59        | (v2_struct_0 @ sk_D)
% 0.41/0.59        | (v2_struct_0 @ sk_A)
% 0.41/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['107', '110'])).
% 0.41/0.59  thf('112', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf(dt_k1_connsp_2, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.59         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59       ( m1_subset_1 @
% 0.41/0.59         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.59  thf('113', plain,
% 0.41/0.59      (![X21 : $i, X22 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X21)
% 0.41/0.59          | ~ (v2_pre_topc @ X21)
% 0.41/0.59          | (v2_struct_0 @ X21)
% 0.41/0.59          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.41/0.59          | (m1_subset_1 @ (k1_connsp_2 @ X21 @ X22) @ 
% 0.41/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.41/0.59  thf('114', plain,
% 0.41/0.59      (((m1_subset_1 @ (k1_connsp_2 @ sk_D @ sk_E) @ 
% 0.41/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.41/0.59        | (v2_struct_0 @ sk_D)
% 0.41/0.59        | ~ (v2_pre_topc @ sk_D)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_D))),
% 0.41/0.59      inference('sup-', [status(thm)], ['112', '113'])).
% 0.41/0.59  thf('115', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.59  thf('116', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.59  thf('117', plain,
% 0.41/0.59      (((m1_subset_1 @ (k1_connsp_2 @ sk_D @ sk_E) @ 
% 0.41/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.41/0.59        | (v2_struct_0 @ sk_D))),
% 0.41/0.59      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.41/0.59  thf('118', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('119', plain,
% 0.41/0.59      ((m1_subset_1 @ (k1_connsp_2 @ sk_D @ sk_E) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.41/0.59      inference('clc', [status(thm)], ['117', '118'])).
% 0.41/0.59  thf(t5_subset, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.41/0.59          ( v1_xboole_0 @ C ) ) ))).
% 0.41/0.59  thf('120', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X11 @ X12)
% 0.41/0.59          | ~ (v1_xboole_0 @ X13)
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t5_subset])).
% 0.41/0.59  thf('121', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D @ sk_E)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['119', '120'])).
% 0.41/0.59  thf('122', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((v2_struct_0 @ sk_A)
% 0.41/0.59          | (v2_struct_0 @ sk_D)
% 0.41/0.59          | (v2_struct_0 @ sk_B_1)
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_D @ sk_E)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['111', '121'])).
% 0.41/0.59  thf('123', plain,
% 0.41/0.59      (((v2_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['19', '122'])).
% 0.41/0.59  thf('124', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('125', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D))),
% 0.41/0.59      inference('clc', [status(thm)], ['123', '124'])).
% 0.41/0.59  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('127', plain, ((v2_struct_0 @ sk_D)),
% 0.41/0.59      inference('clc', [status(thm)], ['125', '126'])).
% 0.41/0.59  thf('128', plain, ($false), inference('demod', [status(thm)], ['0', '127'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
