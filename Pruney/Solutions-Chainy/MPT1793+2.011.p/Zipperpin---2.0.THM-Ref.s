%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzSJ55VzQS

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 309 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          : 1490 (6405 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r2_hidden @ X18 @ ( k1_connsp_2 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('5',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['2','8','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ sk_D @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('25',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r2_hidden @ X28 @ X26 )
      | ( r1_tmap_1 @ X27 @ ( k6_tmap_1 @ X27 @ X26 ) @ ( k7_tmap_1 @ X27 @ X26 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t108_tmap_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_D )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['61','62'])).

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

thf('64',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ( X34 != X31 )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('65',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X31 )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
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
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('71',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('79',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('87',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('95',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','76','84','92','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['35','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
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

thf('111',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('112',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['109','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r2_hidden @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r2_hidden @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','123'])).

thf('125',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzSJ55VzQS
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 103 iterations in 0.059s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.22/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.22/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.52  thf(t109_tmap_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.52               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.22/0.52                 ( ![D:$i]:
% 0.22/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                     ( r1_tmap_1 @
% 0.22/0.52                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.22/0.52                       ( k2_tmap_1 @
% 0.22/0.52                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.22/0.52                       D ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52            ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.52                  ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.22/0.52                    ( ![D:$i]:
% 0.22/0.52                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                        ( r1_tmap_1 @
% 0.22/0.52                          C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.22/0.52                          ( k2_tmap_1 @
% 0.22/0.52                            A @ ( k6_tmap_1 @ A @ B ) @ 
% 0.22/0.52                            ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.22/0.52                          D ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t109_tmap_1])).
% 0.22/0.52  thf('0', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t30_connsp_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.22/0.52          | (r2_hidden @ X18 @ (k1_connsp_2 @ X19 @ X18))
% 0.22/0.52          | ~ (l1_pre_topc @ X19)
% 0.22/0.52          | ~ (v2_pre_topc @ X19)
% 0.22/0.52          | (v2_struct_0 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_C_1)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_C_1)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_C_1)
% 0.22/0.52        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('3', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X9 @ X10)
% 0.22/0.52          | (v2_pre_topc @ X9)
% 0.22/0.52          | ~ (l1_pre_topc @ X10)
% 0.22/0.52          | ~ (v2_pre_topc @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (v2_pre_topc @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain, ((v2_pre_topc @ sk_C_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.52  thf('9', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_m1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X11 @ X12)
% 0.22/0.52          | (l1_pre_topc @ X11)
% 0.22/0.52          | ~ (l1_pre_topc @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.52  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_C_1)
% 0.22/0.52        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['2', '8', '13'])).
% 0.22/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D))),
% 0.22/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k1_connsp_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @
% 0.22/0.52         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X16)
% 0.22/0.52          | ~ (v2_pre_topc @ X16)
% 0.22/0.52          | (v2_struct_0 @ X16)
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.52          | (m1_subset_1 @ (k1_connsp_2 @ X16 @ X17) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_C_1)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_C_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((~ (v2_pre_topc @ sk_C_1)
% 0.22/0.52        | (m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.22/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain, ((v2_pre_topc @ sk_C_1)),
% 0.22/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf(t5_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X6 @ X7)
% 0.22/0.52          | ~ (v1_xboole_0 @ X8)
% 0.22/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain, ((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t2_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         ((r2_hidden @ X4 @ X5)
% 0.22/0.52          | (v1_xboole_0 @ X5)
% 0.22/0.52          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.52        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf(t3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.52          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.22/0.52          | ~ (r2_hidden @ sk_D @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((~ (r2_hidden @ sk_D @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '33'])).
% 0.22/0.52  thf('35', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t55_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.52               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X13)
% 0.22/0.52          | ~ (m1_pre_topc @ X13 @ X14)
% 0.22/0.52          | (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.22/0.52          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.22/0.52          | ~ (l1_pre_topc @ X14)
% 0.22/0.52          | (v2_struct_0 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_C_1)
% 0.22/0.52        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.22/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_C_1)
% 0.22/0.52        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A) | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t108_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.52               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.22/0.52                 ( r1_tmap_1 @
% 0.22/0.52                   A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.52          | (r2_hidden @ X28 @ X26)
% 0.22/0.52          | (r1_tmap_1 @ X27 @ (k6_tmap_1 @ X27 @ X26) @ 
% 0.22/0.52             (k7_tmap_1 @ X27 @ X26) @ X28)
% 0.22/0.52          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.22/0.52          | ~ (l1_pre_topc @ X27)
% 0.22/0.52          | ~ (v2_pre_topc @ X27)
% 0.22/0.52          | (v2_struct_0 @ X27))),
% 0.22/0.52      inference('cnf', [status(esa)], [t108_tmap_1])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.22/0.52          | (r2_hidden @ X0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k7_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.22/0.52          | (r2_hidden @ X0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (((r2_hidden @ sk_D @ sk_B)
% 0.22/0.52        | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k7_tmap_1 @ sk_A @ sk_B) @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '52'])).
% 0.22/0.52  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52         (k7_tmap_1 @ sk_A @ sk_B) @ sk_D)
% 0.22/0.52        | (r2_hidden @ sk_D @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['53', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k7_tmap_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52         ( l1_pre_topc @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.22/0.52         ( v1_funct_2 @
% 0.22/0.52           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.52           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.22/0.52         ( m1_subset_1 @
% 0.22/0.52           ( k7_tmap_1 @ A @ B ) @ 
% 0.22/0.52           ( k1_zfmisc_1 @
% 0.22/0.52             ( k2_zfmisc_1 @
% 0.22/0.52               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X22)
% 0.22/0.52          | ~ (v2_pre_topc @ X22)
% 0.22/0.52          | (v2_struct_0 @ X22)
% 0.22/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.52          | (m1_subset_1 @ (k7_tmap_1 @ X22 @ X23) @ 
% 0.22/0.52             (k1_zfmisc_1 @ 
% 0.22/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ 
% 0.22/0.52               (u1_struct_0 @ (k6_tmap_1 @ X22 @ X23))))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52         (k1_zfmisc_1 @ 
% 0.22/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.52  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52         (k1_zfmisc_1 @ 
% 0.22/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.22/0.52  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))),
% 0.22/0.52      inference('clc', [status(thm)], ['61', '62'])).
% 0.22/0.52  thf(t64_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                 ( m1_subset_1 @
% 0.22/0.52                   C @ 
% 0.22/0.52                   ( k1_zfmisc_1 @
% 0.22/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.52                       ( ![F:$i]:
% 0.22/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                           ( ( ( ( E ) = ( F ) ) & 
% 0.22/0.52                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.22/0.52                             ( r1_tmap_1 @
% 0.22/0.52                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X29)
% 0.22/0.52          | ~ (v2_pre_topc @ X29)
% 0.22/0.52          | ~ (l1_pre_topc @ X29)
% 0.22/0.52          | (v2_struct_0 @ X30)
% 0.22/0.52          | ~ (m1_pre_topc @ X30 @ X29)
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.22/0.52          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.22/0.52          | ((X34) != (X31))
% 0.22/0.52          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X34)
% 0.22/0.52          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 0.22/0.52          | ~ (m1_subset_1 @ X33 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.22/0.52          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.22/0.52          | ~ (v1_funct_1 @ X33)
% 0.22/0.52          | ~ (l1_pre_topc @ X32)
% 0.22/0.52          | ~ (v2_pre_topc @ X32)
% 0.22/0.52          | (v2_struct_0 @ X32))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X32)
% 0.22/0.52          | ~ (v2_pre_topc @ X32)
% 0.22/0.52          | ~ (l1_pre_topc @ X32)
% 0.22/0.52          | ~ (v1_funct_1 @ X33)
% 0.22/0.52          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.22/0.52          | ~ (m1_subset_1 @ X33 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.22/0.52          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X31)
% 0.22/0.52          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.22/0.52          | ~ (m1_pre_topc @ X30 @ X29)
% 0.22/0.52          | (v2_struct_0 @ X30)
% 0.22/0.52          | ~ (l1_pre_topc @ X29)
% 0.22/0.52          | ~ (v2_pre_topc @ X29)
% 0.22/0.52          | (v2_struct_0 @ X29))),
% 0.22/0.52      inference('simplify', [status(thm)], ['64'])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.52             X1)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k7_tmap_1 @ sk_A @ sk_B) @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.52          | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['63', '65'])).
% 0.22/0.52  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X22)
% 0.22/0.52          | ~ (v2_pre_topc @ X22)
% 0.22/0.52          | (v2_struct_0 @ X22)
% 0.22/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.52          | (v1_funct_2 @ (k7_tmap_1 @ X22 @ X23) @ (u1_struct_0 @ X22) @ 
% 0.22/0.52             (u1_struct_0 @ (k6_tmap_1 @ X22 @ X23))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.52  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.22/0.52  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('clc', [status(thm)], ['74', '75'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X22)
% 0.22/0.52          | ~ (v2_pre_topc @ X22)
% 0.22/0.52          | (v2_struct_0 @ X22)
% 0.22/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.52          | (v1_funct_1 @ (k7_tmap_1 @ X22 @ X23)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.52  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.22/0.52  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('84', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['82', '83'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k6_tmap_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52         ( l1_pre_topc @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.52         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.52         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X20)
% 0.22/0.52          | ~ (v2_pre_topc @ X20)
% 0.22/0.52          | (v2_struct_0 @ X20)
% 0.22/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.52          | (l1_pre_topc @ (k6_tmap_1 @ X20 @ X21)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.22/0.52  thf('87', plain,
% 0.22/0.52      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.22/0.52  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('90', plain,
% 0.22/0.52      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.22/0.52  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('92', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['90', '91'])).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('94', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X20)
% 0.22/0.52          | ~ (v2_pre_topc @ X20)
% 0.22/0.52          | (v2_struct_0 @ X20)
% 0.22/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.52          | (v2_pre_topc @ (k6_tmap_1 @ X20 @ X21)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.52  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('98', plain,
% 0.22/0.52      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.22/0.52  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('100', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['98', '99'])).
% 0.22/0.52  thf('101', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.52             X1)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k7_tmap_1 @ sk_A @ sk_B) @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['66', '67', '68', '76', '84', '92', '100'])).
% 0.22/0.52  thf('102', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ sk_D @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.52             sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['55', '101'])).
% 0.22/0.52  thf('103', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('104', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ sk_D @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52              (k7_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.22/0.52             sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['102', '103'])).
% 0.22/0.52  thf('105', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.22/0.52        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52            (k7_tmap_1 @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.22/0.52           sk_D)
% 0.22/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52        | (r2_hidden @ sk_D @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '104'])).
% 0.22/0.52  thf('106', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('107', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52            (k7_tmap_1 @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.22/0.52           sk_D)
% 0.22/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52        | (r2_hidden @ sk_D @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['105', '106'])).
% 0.22/0.52  thf('108', plain,
% 0.22/0.52      (~ (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52          (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k7_tmap_1 @ sk_A @ sk_B) @ sk_C_1) @ 
% 0.22/0.52          sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('109', plain,
% 0.22/0.52      (((r2_hidden @ sk_D @ sk_B)
% 0.22/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['107', '108'])).
% 0.22/0.52  thf('110', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(fc4_tmap_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52         ( l1_pre_topc @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52       ( ( ~( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.22/0.52         ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.22/0.52         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.22/0.52  thf('111', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X24)
% 0.22/0.52          | ~ (v2_pre_topc @ X24)
% 0.22/0.52          | (v2_struct_0 @ X24)
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.52          | ~ (v2_struct_0 @ (k6_tmap_1 @ X24 @ X25)))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc4_tmap_1])).
% 0.22/0.52  thf('112', plain,
% 0.22/0.52      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['110', '111'])).
% 0.22/0.52  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('115', plain,
% 0.22/0.52      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.22/0.52  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('117', plain, (~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['115', '116'])).
% 0.22/0.52  thf('118', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | (r2_hidden @ sk_D @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['109', '117'])).
% 0.22/0.52  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('120', plain, (((r2_hidden @ sk_D @ sk_B) | (v2_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('clc', [status(thm)], ['118', '119'])).
% 0.22/0.52  thf('121', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('122', plain, ((r2_hidden @ sk_D @ sk_B)),
% 0.22/0.52      inference('clc', [status(thm)], ['120', '121'])).
% 0.22/0.52  thf('123', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '122'])).
% 0.22/0.52  thf('124', plain,
% 0.22/0.52      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C_1 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '123'])).
% 0.22/0.52  thf('125', plain, ($false), inference('sup-', [status(thm)], ['16', '124'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
