%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dEXN0x8jwD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 300 expanded)
%              Number of leaves         :   35 ( 100 expanded)
%              Depth                    :   20
%              Number of atoms          : 1429 (6266 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t109_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                     => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t109_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r1_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r2_hidden @ X26 @ X24 )
      | ( r1_tmap_1 @ X25 @ ( k6_tmap_1 @ X25 @ X24 ) @ ( k7_tmap_1 @ X25 @ X24 ) @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t108_tmap_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X16 @ ( k1_connsp_2 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('26',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','29','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('42',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['20','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_D ) ),
    inference(clc,[status(thm)],['19','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_D ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

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

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X28 @ X30 @ ( k2_tmap_1 @ X27 @ X30 @ X31 @ X28 ) @ X29 )
      | ( X32 != X29 )
      | ~ ( r1_tmap_1 @ X27 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('64',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_tmap_1 @ X27 @ X30 @ X31 @ X29 )
      | ( r1_tmap_1 @ X28 @ X30 @ ( k2_tmap_1 @ X27 @ X30 @ X31 @ X28 ) @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('78',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('86',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('94',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','75','83','91','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('110',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('111',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['108','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['0','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dEXN0x8jwD
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 193 iterations in 0.115s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.58  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.58  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.21/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(t109_tmap_1, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.58               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.21/0.58                 ( ![D:$i]:
% 0.21/0.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.58                     ( r1_tmap_1 @
% 0.21/0.58                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.21/0.58                       ( k2_tmap_1 @
% 0.21/0.58                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.21/0.58                       D ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58            ( l1_pre_topc @ A ) ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58              ( ![C:$i]:
% 0.21/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.58                  ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.21/0.58                    ( ![D:$i]:
% 0.21/0.58                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.58                        ( r1_tmap_1 @
% 0.21/0.58                          C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.21/0.58                          ( k2_tmap_1 @
% 0.21/0.58                            A @ ( k6_tmap_1 @ A @ B ) @ 
% 0.21/0.58                            ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.21/0.58                          D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t109_tmap_1])).
% 0.21/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('2', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t55_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.58               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X11)
% 0.21/0.58          | ~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.58          | (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.58          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.21/0.58          | ~ (l1_pre_topc @ X12)
% 0.21/0.58          | (v2_struct_0 @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X0)
% 0.21/0.58          | ~ (l1_pre_topc @ X0)
% 0.21/0.58          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.58          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_C_1)
% 0.21/0.58        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_C_1)
% 0.21/0.58        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('9', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A) | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('12', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t108_tmap_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.58                 ( r1_tmap_1 @
% 0.21/0.58                   A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.58          | (r2_hidden @ X26 @ X24)
% 0.21/0.58          | (r1_tmap_1 @ X25 @ (k6_tmap_1 @ X25 @ X24) @ 
% 0.21/0.58             (k7_tmap_1 @ X25 @ X24) @ X26)
% 0.21/0.58          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.21/0.58          | ~ (l1_pre_topc @ X25)
% 0.21/0.58          | ~ (v2_pre_topc @ X25)
% 0.21/0.58          | (v2_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [t108_tmap_1])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58             (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.58          | (r2_hidden @ X0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.58  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58             (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.58          | (r2_hidden @ X0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (((r2_hidden @ sk_D @ sk_B)
% 0.21/0.58        | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58           (k7_tmap_1 @ sk_A @ sk_B) @ sk_D)
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '18'])).
% 0.21/0.58  thf('20', plain, ((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('21', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t30_connsp_2, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.58           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.58          | (r2_hidden @ X16 @ (k1_connsp_2 @ X17 @ X16))
% 0.21/0.58          | ~ (l1_pre_topc @ X17)
% 0.21/0.58          | ~ (v2_pre_topc @ X17)
% 0.21/0.58          | (v2_struct_0 @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_C_1)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_C_1)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_C_1)
% 0.21/0.58        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf('24', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc1_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i]:
% 0.21/0.58         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.58          | (v2_pre_topc @ X7)
% 0.21/0.58          | ~ (l1_pre_topc @ X8)
% 0.21/0.58          | ~ (v2_pre_topc @ X8))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v2_pre_topc @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('29', plain, ((v2_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.58  thf('30', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_m1_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i]:
% 0.21/0.58         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.58          | (l1_pre_topc @ X9)
% 0.21/0.58          | ~ (l1_pre_topc @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.58  thf('32', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('34', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_C_1)
% 0.21/0.58        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.21/0.58      inference('demod', [status(thm)], ['23', '29', '34'])).
% 0.21/0.58  thf('36', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('37', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D))),
% 0.21/0.58      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('38', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_k1_connsp_2, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58       ( m1_subset_1 @
% 0.21/0.58         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X14 : $i, X15 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X14)
% 0.21/0.58          | ~ (v2_pre_topc @ X14)
% 0.21/0.58          | (v2_struct_0 @ X14)
% 0.21/0.58          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.21/0.58          | (m1_subset_1 @ (k1_connsp_2 @ X14 @ X15) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.21/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.58        | (v2_struct_0 @ sk_C_1)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_C_1)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.58  thf('41', plain, ((v2_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.58  thf('42', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.21/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.58        | (v2_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.58  thf('44', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      ((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.21/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.58      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf(l3_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.58          | (r2_hidden @ X4 @ X6)
% 0.21/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.58          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.58  thf('48', plain, ((r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['37', '47'])).
% 0.21/0.58  thf(t3_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.58          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.21/0.58          | ~ (r2_hidden @ sk_D @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.58  thf('51', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58           (k7_tmap_1 @ sk_A @ sk_B) @ sk_D))),
% 0.21/0.58      inference('clc', [status(thm)], ['19', '51'])).
% 0.21/0.58  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      ((r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58        (k7_tmap_1 @ sk_A @ sk_B) @ sk_D)),
% 0.21/0.58      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_k7_tmap_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58         ( l1_pre_topc @ A ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.21/0.58         ( v1_funct_2 @
% 0.21/0.58           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.58           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.58         ( m1_subset_1 @
% 0.21/0.58           ( k7_tmap_1 @ A @ B ) @ 
% 0.21/0.58           ( k1_zfmisc_1 @
% 0.21/0.58             ( k2_zfmisc_1 @
% 0.21/0.58               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X20)
% 0.21/0.58          | ~ (v2_pre_topc @ X20)
% 0.21/0.58          | (v2_struct_0 @ X20)
% 0.21/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.58          | (m1_subset_1 @ (k7_tmap_1 @ X20 @ X21) @ 
% 0.21/0.58             (k1_zfmisc_1 @ 
% 0.21/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ 
% 0.21/0.58               (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.58  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.58  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.58  thf(t64_tmap_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.58             ( l1_pre_topc @ B ) ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.58                 ( m1_subset_1 @
% 0.21/0.58                   C @ 
% 0.21/0.58                   ( k1_zfmisc_1 @
% 0.21/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.58               ( ![D:$i]:
% 0.21/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.58                   ( ![E:$i]:
% 0.21/0.58                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.58                       ( ![F:$i]:
% 0.21/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.58                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.58                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.58                             ( r1_tmap_1 @
% 0.21/0.58                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X27)
% 0.21/0.58          | ~ (v2_pre_topc @ X27)
% 0.21/0.58          | ~ (l1_pre_topc @ X27)
% 0.21/0.58          | (v2_struct_0 @ X28)
% 0.21/0.58          | ~ (m1_pre_topc @ X28 @ X27)
% 0.21/0.58          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.21/0.58          | (r1_tmap_1 @ X28 @ X30 @ (k2_tmap_1 @ X27 @ X30 @ X31 @ X28) @ X29)
% 0.21/0.58          | ((X32) != (X29))
% 0.21/0.58          | ~ (r1_tmap_1 @ X27 @ X30 @ X31 @ X32)
% 0.21/0.58          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X27))
% 0.21/0.58          | ~ (m1_subset_1 @ X31 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30))))
% 0.21/0.58          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30))
% 0.21/0.58          | ~ (v1_funct_1 @ X31)
% 0.21/0.58          | ~ (l1_pre_topc @ X30)
% 0.21/0.58          | ~ (v2_pre_topc @ X30)
% 0.21/0.58          | (v2_struct_0 @ X30))),
% 0.21/0.58      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.58         ((v2_struct_0 @ X30)
% 0.21/0.58          | ~ (v2_pre_topc @ X30)
% 0.21/0.58          | ~ (l1_pre_topc @ X30)
% 0.21/0.58          | ~ (v1_funct_1 @ X31)
% 0.21/0.58          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30))
% 0.21/0.58          | ~ (m1_subset_1 @ X31 @ 
% 0.21/0.58               (k1_zfmisc_1 @ 
% 0.21/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X30))))
% 0.21/0.58          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 0.21/0.58          | ~ (r1_tmap_1 @ X27 @ X30 @ X31 @ X29)
% 0.21/0.58          | (r1_tmap_1 @ X28 @ X30 @ (k2_tmap_1 @ X27 @ X30 @ X31 @ X28) @ X29)
% 0.21/0.58          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.21/0.58          | ~ (m1_pre_topc @ X28 @ X27)
% 0.21/0.58          | (v2_struct_0 @ X28)
% 0.21/0.58          | ~ (l1_pre_topc @ X27)
% 0.21/0.58          | ~ (v2_pre_topc @ X27)
% 0.21/0.58          | (v2_struct_0 @ X27))),
% 0.21/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.58          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.58             X1)
% 0.21/0.58          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58               (k7_tmap_1 @ sk_A @ sk_B) @ X1)
% 0.21/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.58          | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['62', '64'])).
% 0.21/0.58  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X20)
% 0.21/0.58          | ~ (v2_pre_topc @ X20)
% 0.21/0.58          | (v2_struct_0 @ X20)
% 0.21/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.58          | (v1_funct_2 @ (k7_tmap_1 @ X20 @ X21) @ (u1_struct_0 @ X20) @ 
% 0.21/0.58             (u1_struct_0 @ (k6_tmap_1 @ X20 @ X21))))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.58  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.21/0.58  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('75', plain,
% 0.21/0.58      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.58  thf('76', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('77', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X20)
% 0.21/0.58          | ~ (v2_pre_topc @ X20)
% 0.21/0.58          | (v2_struct_0 @ X20)
% 0.21/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.58          | (v1_funct_1 @ (k7_tmap_1 @ X20 @ X21)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.21/0.58  thf('78', plain,
% 0.21/0.58      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.58  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('81', plain,
% 0.21/0.58      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.21/0.58  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('83', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.58      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.58  thf('84', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_k6_tmap_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58         ( l1_pre_topc @ A ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.21/0.58         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.21/0.58         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.58  thf('85', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X18)
% 0.21/0.58          | ~ (v2_pre_topc @ X18)
% 0.21/0.58          | (v2_struct_0 @ X18)
% 0.21/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.58          | (l1_pre_topc @ (k6_tmap_1 @ X18 @ X19)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.21/0.58  thf('86', plain,
% 0.21/0.58      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.58  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('89', plain,
% 0.21/0.58      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.21/0.58  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('91', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.58      inference('clc', [status(thm)], ['89', '90'])).
% 0.21/0.58  thf('92', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('93', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X18)
% 0.21/0.58          | ~ (v2_pre_topc @ X18)
% 0.21/0.58          | (v2_struct_0 @ X18)
% 0.21/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.58          | (v2_pre_topc @ (k6_tmap_1 @ X18 @ X19)))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.21/0.58  thf('94', plain,
% 0.21/0.58      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.58  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('97', plain,
% 0.21/0.58      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.21/0.58  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('99', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.58      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.58  thf('100', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((v2_struct_0 @ sk_A)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.58          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.58             X1)
% 0.21/0.58          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58               (k7_tmap_1 @ sk_A @ sk_B) @ X1)
% 0.21/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)],
% 0.21/0.58                ['65', '66', '67', '75', '83', '91', '99'])).
% 0.21/0.58  thf('101', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.21/0.58          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.58             sk_D)
% 0.21/0.58          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['54', '100'])).
% 0.21/0.58  thf('102', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.58      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('103', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.58             sk_D)
% 0.21/0.58          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.58          | (v2_struct_0 @ X0)
% 0.21/0.58          | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.58  thf('104', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_C_1)
% 0.21/0.58        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.21/0.58        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58            (k7_tmap_1 @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.21/0.58           sk_D)
% 0.21/0.58        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '103'])).
% 0.21/0.58  thf('105', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('106', plain,
% 0.21/0.58      (((v2_struct_0 @ sk_A)
% 0.21/0.58        | (v2_struct_0 @ sk_C_1)
% 0.21/0.58        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58            (k7_tmap_1 @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.21/0.58           sk_D)
% 0.21/0.58        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['104', '105'])).
% 0.21/0.58  thf('107', plain,
% 0.21/0.58      (~ (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58          (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.58           (k7_tmap_1 @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.21/0.58          sk_D)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('108', plain,
% 0.21/0.58      (((v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58        | (v2_struct_0 @ sk_C_1)
% 0.21/0.58        | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.58  thf('109', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(fc4_tmap_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.58         ( l1_pre_topc @ A ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58       ( ( ~( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.58         ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.21/0.58         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.58  thf('110', plain,
% 0.21/0.58      (![X22 : $i, X23 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X22)
% 0.21/0.58          | ~ (v2_pre_topc @ X22)
% 0.21/0.58          | (v2_struct_0 @ X22)
% 0.21/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.58          | ~ (v2_struct_0 @ (k6_tmap_1 @ X22 @ X23)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc4_tmap_1])).
% 0.21/0.58  thf('111', plain,
% 0.21/0.58      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.21/0.58        | (v2_struct_0 @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.58  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('114', plain,
% 0.21/0.58      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.21/0.58  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('116', plain, (~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.58      inference('clc', [status(thm)], ['114', '115'])).
% 0.21/0.58  thf('117', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.21/0.58      inference('clc', [status(thm)], ['108', '116'])).
% 0.21/0.58  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('119', plain, ((v2_struct_0 @ sk_C_1)),
% 0.21/0.58      inference('clc', [status(thm)], ['117', '118'])).
% 0.21/0.58  thf('120', plain, ($false), inference('demod', [status(thm)], ['0', '119'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
