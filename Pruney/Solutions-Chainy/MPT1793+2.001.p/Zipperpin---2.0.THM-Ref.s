%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J2B9BdSA5O

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 311 expanded)
%              Number of leaves         :   38 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          : 1489 (6404 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ X20 @ ( k1_connsp_2 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('23',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r2_hidden @ X30 @ X28 )
      | ( r1_tmap_1 @ X29 @ ( k6_tmap_1 @ X29 @ X28 ) @ ( k7_tmap_1 @ X29 @ X28 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t108_tmap_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_D @ sk_B_1 )
    | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X24 @ X25 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

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

thf('65',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ( X36 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('66',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r1_tmap_1 @ X31 @ X34 @ X35 @ X33 )
      | ( r1_tmap_1 @ X32 @ X34 @ ( k2_tmap_1 @ X31 @ X34 @ X35 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('72',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('80',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('87',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('88',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('96',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','77','85','93','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B_1 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B_1 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r2_hidden @ sk_D @ sk_B_1 )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('112',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('113',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r2_hidden @ sk_D @ sk_B_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    r2_hidden @ sk_D @ sk_B_1 ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','123'])).

thf('125',plain,(
    v1_xboole_0 @ ( k1_connsp_2 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['18','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J2B9BdSA5O
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 140 iterations in 0.062s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.21/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(t109_tmap_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                     ( r1_tmap_1 @
% 0.21/0.52                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.21/0.52                       ( k2_tmap_1 @
% 0.21/0.52                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.21/0.52                       D ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52                  ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.21/0.52                    ( ![D:$i]:
% 0.21/0.52                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.52                        ( r1_tmap_1 @
% 0.21/0.52                          C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.21/0.52                          ( k2_tmap_1 @
% 0.21/0.52                            A @ ( k6_tmap_1 @ A @ B ) @ 
% 0.21/0.52                            ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.21/0.52                          D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t109_tmap_1])).
% 0.21/0.52  thf('0', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t30_connsp_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.21/0.52          | (r2_hidden @ X20 @ (k1_connsp_2 @ X21 @ X20))
% 0.21/0.52          | ~ (l1_pre_topc @ X21)
% 0.21/0.52          | ~ (v2_pre_topc @ X21)
% 0.21/0.52          | (v2_struct_0 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C_1)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_C_1)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_C_1)
% 0.21/0.52        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.52          | (v2_pre_topc @ X11)
% 0.21/0.52          | ~ (l1_pre_topc @ X12)
% 0.21/0.52          | ~ (v2_pre_topc @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v2_pre_topc @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain, ((v2_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf('9', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.52          | (l1_pre_topc @ X13)
% 0.21/0.52          | ~ (l1_pre_topc @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C_1)
% 0.21/0.52        | (r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '8', '13'])).
% 0.21/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain, ((r2_hidden @ sk_D @ (k1_connsp_2 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf(d1_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('18', plain, (~ (v1_xboole_0 @ (k1_connsp_2 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k1_connsp_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X18)
% 0.21/0.52          | ~ (v2_pre_topc @ X18)
% 0.21/0.52          | (v2_struct_0 @ X18)
% 0.21/0.52          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.21/0.52          | (m1_subset_1 @ (k1_connsp_2 @ X18 @ X19) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52        | (v2_struct_0 @ sk_C_1)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_C_1)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, ((v2_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.52  thf('23', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52        | (v2_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.21/0.52  thf('25', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.52      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf(cc1_subset_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.52          | (v1_xboole_0 @ X7)
% 0.21/0.52          | ~ (v1_xboole_0 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52        | (v1_xboole_0 @ (k1_connsp_2 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t2_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((r2_hidden @ X9 @ X10)
% 0.21/0.52          | (v1_xboole_0 @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf(t3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ X3)
% 0.21/0.52          | ~ (r2_hidden @ X5 @ X6)
% 0.21/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.21/0.52          | ~ (r2_hidden @ sk_D @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_D @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['29', '34'])).
% 0.21/0.52  thf('36', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t55_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X15)
% 0.21/0.52          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.52          | (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.21/0.52          | ~ (l1_pre_topc @ X16)
% 0.21/0.52          | (v2_struct_0 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C_1)
% 0.21/0.52        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_C_1)
% 0.21/0.52        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A) | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t108_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.52                 ( r1_tmap_1 @
% 0.21/0.52                   A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.52          | (r2_hidden @ X30 @ X28)
% 0.21/0.52          | (r1_tmap_1 @ X29 @ (k6_tmap_1 @ X29 @ X28) @ 
% 0.21/0.52             (k7_tmap_1 @ X29 @ X28) @ X30)
% 0.21/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.21/0.52          | ~ (l1_pre_topc @ X29)
% 0.21/0.52          | ~ (v2_pre_topc @ X29)
% 0.21/0.52          | (v2_struct_0 @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [t108_tmap_1])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52             (k7_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.21/0.52          | (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52             (k7_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.21/0.52          | (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (((r2_hidden @ sk_D @ sk_B_1)
% 0.21/0.52        | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52           (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_D)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '53'])).
% 0.21/0.52  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (((r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52         (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_D)
% 0.21/0.52        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k7_tmap_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.21/0.52         ( v1_funct_2 @
% 0.21/0.52           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.52           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( m1_subset_1 @
% 0.21/0.52           ( k7_tmap_1 @ A @ B ) @ 
% 0.21/0.52           ( k1_zfmisc_1 @
% 0.21/0.52             ( k2_zfmisc_1 @
% 0.21/0.52               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X24)
% 0.21/0.52          | ~ (v2_pre_topc @ X24)
% 0.21/0.52          | (v2_struct_0 @ X24)
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.52          | (m1_subset_1 @ (k7_tmap_1 @ X24 @ X25) @ 
% 0.21/0.52             (k1_zfmisc_1 @ 
% 0.21/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ 
% 0.21/0.52               (u1_struct_0 @ (k6_tmap_1 @ X24 @ X25))))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52         (k1_zfmisc_1 @ 
% 0.21/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52         (k1_zfmisc_1 @ 
% 0.21/0.52          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.52  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.21/0.52      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf(t64_tmap_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.52             ( l1_pre_topc @ B ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.52                 ( m1_subset_1 @
% 0.21/0.52                   C @ 
% 0.21/0.52                   ( k1_zfmisc_1 @
% 0.21/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.52                   ( ![E:$i]:
% 0.21/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.52                       ( ![F:$i]:
% 0.21/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.52                           ( ( ( ( E ) = ( F ) ) & 
% 0.21/0.52                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.21/0.52                             ( r1_tmap_1 @
% 0.21/0.52                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X31)
% 0.21/0.52          | ~ (v2_pre_topc @ X31)
% 0.21/0.52          | ~ (l1_pre_topc @ X31)
% 0.21/0.52          | (v2_struct_0 @ X32)
% 0.21/0.52          | ~ (m1_pre_topc @ X32 @ X31)
% 0.21/0.52          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.21/0.52          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.21/0.52          | ((X36) != (X33))
% 0.21/0.52          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X36)
% 0.21/0.52          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X31))
% 0.21/0.52          | ~ (m1_subset_1 @ X35 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.21/0.52          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.21/0.52          | ~ (v1_funct_1 @ X35)
% 0.21/0.52          | ~ (l1_pre_topc @ X34)
% 0.21/0.52          | ~ (v2_pre_topc @ X34)
% 0.21/0.52          | (v2_struct_0 @ X34))),
% 0.21/0.52      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X34)
% 0.21/0.52          | ~ (v2_pre_topc @ X34)
% 0.21/0.52          | ~ (l1_pre_topc @ X34)
% 0.21/0.52          | ~ (v1_funct_1 @ X35)
% 0.21/0.52          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))
% 0.21/0.52          | ~ (m1_subset_1 @ X35 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X34))))
% 0.21/0.52          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.21/0.52          | ~ (r1_tmap_1 @ X31 @ X34 @ X35 @ X33)
% 0.21/0.52          | (r1_tmap_1 @ X32 @ X34 @ (k2_tmap_1 @ X31 @ X34 @ X35 @ X32) @ X33)
% 0.21/0.52          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.21/0.52          | ~ (m1_pre_topc @ X32 @ X31)
% 0.21/0.52          | (v2_struct_0 @ X32)
% 0.21/0.52          | ~ (l1_pre_topc @ X31)
% 0.21/0.52          | ~ (v2_pre_topc @ X31)
% 0.21/0.52          | (v2_struct_0 @ X31))),
% 0.21/0.52      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.21/0.52             X1)
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52               (k7_tmap_1 @ sk_A @ sk_B_1) @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52               (u1_struct_0 @ sk_A) @ 
% 0.21/0.52               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.21/0.52          | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '66'])).
% 0.21/0.52  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X24)
% 0.21/0.52          | ~ (v2_pre_topc @ X24)
% 0.21/0.52          | (v2_struct_0 @ X24)
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.52          | (v1_funct_2 @ (k7_tmap_1 @ X24 @ X25) @ (u1_struct_0 @ X24) @ 
% 0.21/0.52             (u1_struct_0 @ (k6_tmap_1 @ X24 @ X25))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.21/0.52  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('clc', [status(thm)], ['75', '76'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X24)
% 0.21/0.52          | ~ (v2_pre_topc @ X24)
% 0.21/0.52          | (v2_struct_0 @ X24)
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.52          | (v1_funct_1 @ (k7_tmap_1 @ X24 @ X25)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.21/0.52  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('85', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k6_tmap_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.21/0.52         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.21/0.52         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X22)
% 0.21/0.52          | ~ (v2_pre_topc @ X22)
% 0.21/0.52          | (v2_struct_0 @ X22)
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.52          | (l1_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.52  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.21/0.52  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('93', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['91', '92'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('95', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X22)
% 0.21/0.52          | ~ (v2_pre_topc @ X22)
% 0.21/0.52          | (v2_struct_0 @ X22)
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.52          | (v2_pre_topc @ (k6_tmap_1 @ X22 @ X23)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.52  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('99', plain,
% 0.21/0.52      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.21/0.52  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('101', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.52  thf('102', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v2_struct_0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.21/0.52             X1)
% 0.21/0.52          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52               (k7_tmap_1 @ sk_A @ sk_B_1) @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['67', '68', '69', '77', '85', '93', '101'])).
% 0.21/0.52  thf('103', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ sk_D @ sk_B_1)
% 0.21/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.21/0.52             sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '102'])).
% 0.21/0.52  thf('104', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('105', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ sk_D @ sk_B_1)
% 0.21/0.52          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.21/0.52             sk_D)
% 0.21/0.52          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['103', '104'])).
% 0.21/0.52  thf('106', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_C_1)
% 0.21/0.52        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.21/0.52        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52            (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_C_1) @ 
% 0.21/0.52           sk_D)
% 0.21/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '105'])).
% 0.21/0.52  thf('107', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('108', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_C_1)
% 0.21/0.52        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52            (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_C_1) @ 
% 0.21/0.52           sk_D)
% 0.21/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.52  thf('109', plain,
% 0.21/0.52      (~ (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52          (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.52           (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_C_1) @ 
% 0.21/0.52          sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('110', plain,
% 0.21/0.52      (((r2_hidden @ sk_D @ sk_B_1)
% 0.21/0.52        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v2_struct_0 @ sk_C_1)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.52  thf('111', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(fc4_tmap_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52         ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( ( ~( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.21/0.52         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.52  thf('112', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X26)
% 0.21/0.52          | ~ (v2_pre_topc @ X26)
% 0.21/0.52          | (v2_struct_0 @ X26)
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.52          | ~ (v2_struct_0 @ (k6_tmap_1 @ X26 @ X27)))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc4_tmap_1])).
% 0.21/0.52  thf('113', plain,
% 0.21/0.52      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['111', '112'])).
% 0.21/0.52  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('116', plain,
% 0.21/0.52      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.21/0.52  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('118', plain, (~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['116', '117'])).
% 0.21/0.52  thf('119', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_C_1)
% 0.21/0.52        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['110', '118'])).
% 0.21/0.52  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('121', plain, (((r2_hidden @ sk_D @ sk_B_1) | (v2_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['119', '120'])).
% 0.21/0.52  thf('122', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('123', plain, ((r2_hidden @ sk_D @ sk_B_1)),
% 0.21/0.52      inference('clc', [status(thm)], ['121', '122'])).
% 0.21/0.52  thf('124', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '123'])).
% 0.21/0.52  thf('125', plain, ((v1_xboole_0 @ (k1_connsp_2 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '124'])).
% 0.21/0.52  thf('126', plain, ($false), inference('demod', [status(thm)], ['18', '125'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
