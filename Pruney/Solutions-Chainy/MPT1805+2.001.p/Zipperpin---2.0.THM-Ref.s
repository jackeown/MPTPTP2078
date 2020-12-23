%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8layhbhL5i

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 (1042 expanded)
%              Number of leaves         :   30 ( 316 expanded)
%              Depth                    :   30
%              Number of atoms          : 2710 (35698 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t121_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) )
            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ B @ ( k8_tmap_1 @ A @ B ) )
            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) )
              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ B @ ( k8_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X14 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X8 @ X9 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('16',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('23',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('26',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X13 @ X14 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('34',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13','23','31','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X10 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X8 @ X9 @ X7 @ X10 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('45',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('46',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('47',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13','23','31','39'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('52',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X8 @ X9 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('56',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('57',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('58',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf(t49_tmap_1,axiom,(
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
             => ( ( v5_pre_topc @ C @ B @ A )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( m1_subset_1 @ ( sk_D @ X21 @ X20 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ( v5_pre_topc @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('64',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf(t119_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tmap_1 @ B @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ C ) ) ) ) )).

thf('76',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( r1_tmap_1 @ X17 @ ( k8_tmap_1 @ X18 @ X17 ) @ ( k2_tmap_1 @ X18 @ ( k8_tmap_1 @ X18 @ X17 ) @ ( k9_tmap_1 @ X18 @ X17 ) @ X17 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t119_tmap_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ X1 @ X0 ) @ ( k2_tmap_1 @ X1 @ ( k8_tmap_1 @ X1 @ X0 ) @ ( k9_tmap_1 @ X1 @ X0 ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ X1 @ X0 ) @ ( k2_tmap_1 @ X1 @ ( k8_tmap_1 @ X1 @ X0 ) @ ( k9_tmap_1 @ X1 @ X0 ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('89',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','86','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('98',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( r1_tmap_1 @ X20 @ X22 @ X21 @ ( sk_D @ X21 @ X20 @ X22 ) )
      | ( v5_pre_topc @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('101',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['82','83'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('118',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['115'])).

thf('119',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13','23','31','39'])).

thf('123',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['115'])).

thf('124',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('126',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('128',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['115'])).

thf('129',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('131',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['115'])).

thf('133',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['121','126','131','132'])).

thf('134',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_B ) @ sk_B @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['116','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['137','138'])).

thf(fc5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ~ ( v2_struct_0 @ ( k8_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('140',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( v2_struct_0 @ ( k8_tmap_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_tmap_1])).

thf('141',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['0','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8layhbhL5i
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 83 iterations in 0.063s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.21/0.51  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(t121_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ( v1_funct_1 @
% 0.21/0.51               ( k2_tmap_1 @
% 0.21/0.51                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.21/0.51             ( v1_funct_2 @
% 0.21/0.51               ( k2_tmap_1 @
% 0.21/0.51                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.21/0.51               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.51             ( v5_pre_topc @
% 0.21/0.51               ( k2_tmap_1 @
% 0.21/0.51                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.21/0.51               B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.51             ( m1_subset_1 @
% 0.21/0.51               ( k2_tmap_1 @
% 0.21/0.51                 A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.21/0.51               ( k1_zfmisc_1 @
% 0.21/0.51                 ( k2_zfmisc_1 @
% 0.21/0.51                   ( u1_struct_0 @ B ) @ 
% 0.21/0.51                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51              ( ( v1_funct_1 @
% 0.21/0.51                  ( k2_tmap_1 @
% 0.21/0.51                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) ) & 
% 0.21/0.51                ( v1_funct_2 @
% 0.21/0.51                  ( k2_tmap_1 @
% 0.21/0.51                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.21/0.51                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.51                ( v5_pre_topc @
% 0.21/0.51                  ( k2_tmap_1 @
% 0.21/0.51                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.21/0.51                  B @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.51                ( m1_subset_1 @
% 0.21/0.51                  ( k2_tmap_1 @
% 0.21/0.51                    A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.21/0.51                  ( k1_zfmisc_1 @
% 0.21/0.51                    ( k2_zfmisc_1 @
% 0.21/0.51                      ( u1_struct_0 @ B ) @ 
% 0.21/0.51                      ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t121_tmap_1])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k9_tmap_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.21/0.51         ( v1_funct_2 @
% 0.21/0.51           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.51           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           ( k9_tmap_1 @ A @ B ) @ 
% 0.21/0.51           ( k1_zfmisc_1 @
% 0.21/0.51             ( k2_zfmisc_1 @
% 0.21/0.51               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X13)
% 0.21/0.51          | ~ (v2_pre_topc @ X13)
% 0.21/0.51          | (v2_struct_0 @ X13)
% 0.21/0.51          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.51          | (m1_subset_1 @ (k9_tmap_1 @ X13 @ X14) @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.51               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X14))))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.51  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf(dt_k2_tmap_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.21/0.51         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           C @ 
% 0.21/0.51           ( k1_zfmisc_1 @
% 0.21/0.51             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.21/0.51         ( l1_struct_0 @ D ) ) =>
% 0.21/0.51       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.51         ( v1_funct_2 @
% 0.21/0.51           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.21/0.51           ( u1_struct_0 @ B ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.21/0.51           ( k1_zfmisc_1 @
% 0.21/0.51             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.21/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (l1_struct_0 @ X9)
% 0.21/0.51          | ~ (l1_struct_0 @ X8)
% 0.21/0.51          | ~ (l1_struct_0 @ X10)
% 0.21/0.51          | (v1_funct_1 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (l1_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('12', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k8_tmap_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.51         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.51         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X11)
% 0.21/0.51          | ~ (v2_pre_topc @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | ~ (m1_pre_topc @ X12 @ X11)
% 0.21/0.51          | (l1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.51  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('23', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X13)
% 0.21/0.51          | ~ (v2_pre_topc @ X13)
% 0.21/0.51          | (v2_struct_0 @ X13)
% 0.21/0.51          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.51          | (v1_funct_1 @ (k9_tmap_1 @ X13 @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.51  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X13)
% 0.21/0.51          | ~ (v2_pre_topc @ X13)
% 0.21/0.51          | (v2_struct_0 @ X13)
% 0.21/0.51          | ~ (m1_pre_topc @ X14 @ X13)
% 0.21/0.51          | (v1_funct_2 @ (k9_tmap_1 @ X13 @ X14) @ (u1_struct_0 @ X13) @ 
% 0.21/0.51             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X14))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.51  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '13', '23', '31', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.21/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (l1_struct_0 @ X9)
% 0.21/0.51          | ~ (l1_struct_0 @ X8)
% 0.21/0.51          | ~ (l1_struct_0 @ X10)
% 0.21/0.51          | (v1_funct_2 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.21/0.51             (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (l1_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('45', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('46', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.21/0.51  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '13', '23', '31', '39'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X7 @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.21/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (l1_struct_0 @ X9)
% 0.21/0.51          | ~ (l1_struct_0 @ X8)
% 0.21/0.51          | ~ (l1_struct_0 @ X10)
% 0.21/0.51          | (m1_subset_1 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.51             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.51          | ~ (l1_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.51          | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('56', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('57', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.51             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.21/0.51  thf(t49_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X20)
% 0.21/0.51          | ~ (v2_pre_topc @ X20)
% 0.21/0.51          | ~ (l1_pre_topc @ X20)
% 0.21/0.51          | (m1_subset_1 @ (sk_D @ X21 @ X20 @ X22) @ (u1_struct_0 @ X20))
% 0.21/0.51          | (v5_pre_topc @ X21 @ X20 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))))
% 0.21/0.51          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 0.21/0.51          | ~ (v1_funct_1 @ X21)
% 0.21/0.51          | ~ (l1_pre_topc @ X22)
% 0.21/0.51          | ~ (v2_pre_topc @ X22)
% 0.21/0.51          | (v2_struct_0 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (v1_funct_2 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X11)
% 0.21/0.51          | ~ (v2_pre_topc @ X11)
% 0.21/0.51          | (v2_struct_0 @ X11)
% 0.21/0.51          | ~ (m1_pre_topc @ X12 @ X11)
% 0.21/0.51          | (v2_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.21/0.51  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('69', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf('70', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (v1_funct_2 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '69', '70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ X0))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ X0))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (m1_subset_1 @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.21/0.51             (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.51  thf(t119_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51               ( r1_tmap_1 @
% 0.21/0.51                 B @ ( k8_tmap_1 @ A @ B ) @ 
% 0.21/0.51                 ( k2_tmap_1 @
% 0.21/0.51                   A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ B ) @ 
% 0.21/0.51                 C ) ) ) ) ) ))).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X17)
% 0.21/0.51          | ~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.51          | (r1_tmap_1 @ X17 @ (k8_tmap_1 @ X18 @ X17) @ 
% 0.21/0.51             (k2_tmap_1 @ X18 @ (k8_tmap_1 @ X18 @ X17) @ 
% 0.21/0.51              (k9_tmap_1 @ X18 @ X17) @ X17) @ 
% 0.21/0.51             X19)
% 0.21/0.51          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.51          | ~ (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (v2_pre_topc @ X18)
% 0.21/0.51          | (v2_struct_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t119_tmap_1])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ X1)
% 0.21/0.51          | ~ (v2_pre_topc @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ X1 @ X0) @ 
% 0.21/0.51             (k2_tmap_1 @ X1 @ (k8_tmap_1 @ X1 @ X0) @ (k9_tmap_1 @ X1 @ X0) @ 
% 0.21/0.51              X0) @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ X1 @ X0) @ 
% 0.21/0.51             (k2_tmap_1 @ X1 @ (k8_tmap_1 @ X1 @ X0) @ (k9_tmap_1 @ X1 @ X0) @ 
% 0.21/0.51              X0) @ 
% 0.21/0.51             (sk_D @ 
% 0.21/0.51              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51              X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (v2_pre_topc @ X1)
% 0.21/0.51          | (v2_struct_0 @ X1)
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((~ (l1_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           (sk_D @ 
% 0.21/0.51            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51            sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '78'])).
% 0.21/0.51  thf('80', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('82', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.51  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('85', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('86', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('87', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.51          | (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (v2_pre_topc @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.51  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('92', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.21/0.51  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (r1_tmap_1 @ sk_B @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           (sk_D @ 
% 0.21/0.51            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51             (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51            sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['79', '86', '92', '93', '94', '95'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.51             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X20)
% 0.21/0.51          | ~ (v2_pre_topc @ X20)
% 0.21/0.51          | ~ (l1_pre_topc @ X20)
% 0.21/0.51          | ~ (r1_tmap_1 @ X20 @ X22 @ X21 @ (sk_D @ X21 @ X20 @ X22))
% 0.21/0.51          | (v5_pre_topc @ X21 @ X20 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))))
% 0.21/0.51          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 0.21/0.51          | ~ (v1_funct_1 @ X21)
% 0.21/0.51          | ~ (l1_pre_topc @ X22)
% 0.21/0.51          | ~ (v2_pre_topc @ X22)
% 0.21/0.51          | (v2_struct_0 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (v1_funct_2 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51               (sk_D @ 
% 0.21/0.51                (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                 (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51                X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.51  thf('100', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf('101', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (v1_funct_2 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51          | ~ (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51               (sk_D @ 
% 0.21/0.51                (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                 (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51                X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | (v2_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | ~ (v1_funct_2 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51        | ~ (v1_funct_1 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['96', '102'])).
% 0.21/0.51  thf('104', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.21/0.51  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | ~ (v1_funct_2 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51        | ~ (v1_funct_1 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.51        | ~ (v1_funct_2 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['107'])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      ((~ (l1_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v1_funct_1 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '108'])).
% 0.21/0.51  thf('110', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v1_funct_1 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['109', '110'])).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      ((~ (l1_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '111'])).
% 0.21/0.51  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['112', '113'])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))
% 0.21/0.51        | ~ (v1_funct_2 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51        | ~ (v5_pre_topc @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51             sk_B @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | ~ (m1_subset_1 @ 
% 0.21/0.51             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51              (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('116', plain,
% 0.21/0.51      ((~ (v5_pre_topc @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v5_pre_topc @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51               sk_B @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['115'])).
% 0.21/0.51  thf('117', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.51             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      ((~ (m1_subset_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.21/0.51      inference('split', [status(esa)], ['115'])).
% 0.21/0.51  thf('119', plain,
% 0.21/0.51      ((~ (l1_struct_0 @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.51  thf('120', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('121', plain,
% 0.21/0.51      (((m1_subset_1 @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.21/0.51      inference('demod', [status(thm)], ['119', '120'])).
% 0.21/0.51  thf('122', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '13', '23', '31', '39'])).
% 0.21/0.51  thf('123', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['115'])).
% 0.21/0.51  thf('124', plain,
% 0.21/0.51      ((~ (l1_struct_0 @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_1 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.51  thf('125', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('126', plain,
% 0.21/0.51      (((v1_funct_1 @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['124', '125'])).
% 0.21/0.51  thf('127', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_funct_2 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.21/0.51           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.21/0.51          | ~ (l1_struct_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.21/0.51  thf('128', plain,
% 0.21/0.51      ((~ (v1_funct_2 @ 
% 0.21/0.51           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51            (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('split', [status(esa)], ['115'])).
% 0.21/0.51  thf('129', plain,
% 0.21/0.51      ((~ (l1_struct_0 @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ 
% 0.21/0.51               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51                (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['127', '128'])).
% 0.21/0.51  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('131', plain,
% 0.21/0.51      (((v1_funct_2 @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['129', '130'])).
% 0.21/0.51  thf('132', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((v5_pre_topc @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51         sk_B @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((v1_funct_2 @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((v1_funct_1 @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((m1_subset_1 @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.21/0.51      inference('split', [status(esa)], ['115'])).
% 0.21/0.51  thf('133', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((v5_pre_topc @ 
% 0.21/0.51         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51          (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51         sk_B @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['121', '126', '131', '132'])).
% 0.21/0.51  thf('134', plain,
% 0.21/0.51      (~ (v5_pre_topc @ 
% 0.21/0.51          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.21/0.51           (k9_tmap_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.51          sk_B @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['116', '133'])).
% 0.21/0.51  thf('135', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['114', '134'])).
% 0.21/0.51  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('137', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['135', '136'])).
% 0.21/0.51  thf('138', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('139', plain, ((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['137', '138'])).
% 0.21/0.51  thf(fc5_tmap_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51       ( ( ~( v2_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.21/0.51         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.21/0.51  thf('140', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X15)
% 0.21/0.51          | ~ (v2_pre_topc @ X15)
% 0.21/0.51          | (v2_struct_0 @ X15)
% 0.21/0.51          | ~ (m1_pre_topc @ X16 @ X15)
% 0.21/0.51          | ~ (v2_struct_0 @ (k8_tmap_1 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc5_tmap_1])).
% 0.21/0.51  thf('141', plain,
% 0.21/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['139', '140'])).
% 0.21/0.51  thf('142', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('145', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.21/0.51  thf('146', plain, ($false), inference('demod', [status(thm)], ['0', '145'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
