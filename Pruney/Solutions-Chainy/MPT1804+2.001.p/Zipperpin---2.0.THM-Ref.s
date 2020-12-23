%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KDNvKyJ2wg

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:00 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  185 (1053 expanded)
%              Number of leaves         :   32 ( 320 expanded)
%              Depth                    :   33
%              Number of atoms          : 2929 (39521 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t120_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tsep_1 @ B @ C )
               => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) )
                  & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                  & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ C @ ( k8_tmap_1 @ A @ B ) )
                  & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( r1_tsep_1 @ B @ C )
                 => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) )
                    & ( v1_funct_2 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                    & ( v5_pre_topc @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ C @ ( k8_tmap_1 @ A @ B ) )
                    & ( m1_subset_1 @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t120_tmap_1])).

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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13','23','31','39'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('53',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( l1_struct_0 @ X10 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X8 @ X9 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('57',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('58',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('59',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

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

thf('61',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X21 @ X23 ) @ ( u1_struct_0 @ X21 ) )
      | ( v5_pre_topc @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('62',plain,(
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
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('65',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('72',plain,(
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
    inference(demod,[status(thm)],['62','70','71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['52','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf(t118_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k8_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( r1_tsep_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( r1_tmap_1 @ X19 @ ( k8_tmap_1 @ X18 @ X17 ) @ ( k2_tmap_1 @ X18 @ ( k8_tmap_1 @ X18 @ X17 ) @ ( k9_tmap_1 @ X18 @ X17 ) @ X19 ) @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t118_tmap_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ X1 @ X2 ) @ ( k2_tmap_1 @ X1 @ ( k8_tmap_1 @ X1 @ X2 ) @ ( k9_tmap_1 @ X1 @ X2 ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tsep_1 @ X2 @ X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( r1_tsep_1 @ X2 @ X0 )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ X1 @ X2 ) @ ( k2_tmap_1 @ X1 @ ( k8_tmap_1 @ X1 @ X2 ) @ ( k9_tmap_1 @ X1 @ X2 ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','83'])).

thf('85',plain,(
    r1_tsep_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('87',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('93',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['88','89'])).

thf('98',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('99',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85','90','96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('102',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( r1_tmap_1 @ X21 @ X23 @ X22 @ ( sk_D @ X22 @ X21 @ X23 ) )
      | ( v5_pre_topc @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('103',plain,(
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
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('105',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('106',plain,(
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
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('109',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['88','89'])).

thf('110',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('122',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['119'])).

thf('123',plain,
    ( ~ ( l1_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('127',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['119'])).

thf('128',plain,
    ( ~ ( l1_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('130',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13','23','31','39'])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(split,[status(esa)],['119'])).

thf('133',plain,
    ( ~ ( l1_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('135',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['119'])).

thf('137',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['125','130','135','136'])).

thf('138',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['120','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['118','138'])).

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
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
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

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['0','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KDNvKyJ2wg
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 111 iterations in 0.119s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.40/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.40/0.58  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.40/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.58  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.40/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.40/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.58  thf(t120_tmap_1, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.58               ( ( r1_tsep_1 @ B @ C ) =>
% 0.40/0.58                 ( ( v1_funct_1 @
% 0.40/0.58                     ( k2_tmap_1 @
% 0.40/0.58                       A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) ) & 
% 0.40/0.58                   ( v1_funct_2 @
% 0.40/0.58                     ( k2_tmap_1 @
% 0.40/0.58                       A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 0.40/0.58                     ( u1_struct_0 @ C ) @ 
% 0.40/0.58                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.40/0.58                   ( v5_pre_topc @
% 0.40/0.58                     ( k2_tmap_1 @
% 0.40/0.58                       A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 0.40/0.58                     C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.40/0.58                   ( m1_subset_1 @
% 0.40/0.58                     ( k2_tmap_1 @
% 0.40/0.58                       A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 0.40/0.58                     ( k1_zfmisc_1 @
% 0.40/0.58                       ( k2_zfmisc_1 @
% 0.40/0.58                         ( u1_struct_0 @ C ) @ 
% 0.40/0.58                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.58            ( l1_pre_topc @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.58              ( ![C:$i]:
% 0.40/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.58                  ( ( r1_tsep_1 @ B @ C ) =>
% 0.40/0.58                    ( ( v1_funct_1 @
% 0.40/0.58                        ( k2_tmap_1 @
% 0.40/0.58                          A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) ) & 
% 0.40/0.58                      ( v1_funct_2 @
% 0.40/0.58                        ( k2_tmap_1 @
% 0.40/0.58                          A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 0.40/0.58                        ( u1_struct_0 @ C ) @ 
% 0.40/0.58                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.40/0.58                      ( v5_pre_topc @
% 0.40/0.58                        ( k2_tmap_1 @
% 0.40/0.58                          A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 0.40/0.58                        C @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.40/0.58                      ( m1_subset_1 @
% 0.40/0.58                        ( k2_tmap_1 @
% 0.40/0.58                          A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 0.40/0.58                        ( k1_zfmisc_1 @
% 0.40/0.58                          ( k2_zfmisc_1 @
% 0.40/0.58                            ( u1_struct_0 @ C ) @ 
% 0.40/0.58                            ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t120_tmap_1])).
% 0.40/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(dt_k9_tmap_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.58         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.58       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.40/0.58         ( v1_funct_2 @
% 0.40/0.58           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.58           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           ( k9_tmap_1 @ A @ B ) @ 
% 0.40/0.58           ( k1_zfmisc_1 @
% 0.40/0.58             ( k2_zfmisc_1 @
% 0.40/0.58               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X13)
% 0.40/0.58          | ~ (v2_pre_topc @ X13)
% 0.40/0.58          | (v2_struct_0 @ X13)
% 0.40/0.58          | ~ (m1_pre_topc @ X14 @ X13)
% 0.40/0.58          | (m1_subset_1 @ (k9_tmap_1 @ X13 @ X14) @ 
% 0.40/0.58             (k1_zfmisc_1 @ 
% 0.40/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ 
% 0.40/0.58               (u1_struct_0 @ (k8_tmap_1 @ X13 @ X14))))))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58         (k1_zfmisc_1 @ 
% 0.40/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58         (k1_zfmisc_1 @ 
% 0.40/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.40/0.58        | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.40/0.58  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.40/0.58      inference('clc', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(dt_k2_tmap_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.40/0.58         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           C @ 
% 0.40/0.58           ( k1_zfmisc_1 @
% 0.40/0.58             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.40/0.58         ( l1_struct_0 @ D ) ) =>
% 0.40/0.58       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.40/0.58         ( v1_funct_2 @
% 0.40/0.58           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.40/0.58           ( u1_struct_0 @ B ) ) & 
% 0.40/0.58         ( m1_subset_1 @
% 0.40/0.58           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.40/0.58           ( k1_zfmisc_1 @
% 0.40/0.58             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X7 @ 
% 0.40/0.58             (k1_zfmisc_1 @ 
% 0.40/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.40/0.58          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.40/0.58          | ~ (v1_funct_1 @ X7)
% 0.40/0.58          | ~ (l1_struct_0 @ X9)
% 0.40/0.58          | ~ (l1_struct_0 @ X8)
% 0.40/0.58          | ~ (l1_struct_0 @ X10)
% 0.40/0.58          | (v1_funct_1 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_1 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58          | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.58  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(dt_l1_pre_topc, axiom,
% 0.40/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.58  thf('12', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.58  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(dt_k8_tmap_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.58         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.58       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.40/0.58         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.40/0.58         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X11)
% 0.40/0.58          | ~ (v2_pre_topc @ X11)
% 0.40/0.58          | (v2_struct_0 @ X11)
% 0.40/0.58          | ~ (m1_pre_topc @ X12 @ X11)
% 0.40/0.58          | (l1_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.40/0.58  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('21', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('clc', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('22', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.58  thf('23', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X13)
% 0.40/0.58          | ~ (v2_pre_topc @ X13)
% 0.40/0.58          | (v2_struct_0 @ X13)
% 0.40/0.58          | ~ (m1_pre_topc @ X14 @ X13)
% 0.40/0.58          | (v1_funct_1 @ (k9_tmap_1 @ X13 @ X14)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.58  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.40/0.58  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('31', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.40/0.58  thf('32', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i]:
% 0.40/0.58         (~ (l1_pre_topc @ X13)
% 0.40/0.58          | ~ (v2_pre_topc @ X13)
% 0.40/0.58          | (v2_struct_0 @ X13)
% 0.40/0.58          | ~ (m1_pre_topc @ X14 @ X13)
% 0.40/0.58          | (v1_funct_2 @ (k9_tmap_1 @ X13 @ X14) @ (u1_struct_0 @ X13) @ 
% 0.40/0.58             (u1_struct_0 @ (k8_tmap_1 @ X13 @ X14))))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.58        | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.40/0.58  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('clc', [status(thm)], ['37', '38'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_1 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['10', '13', '23', '31', '39'])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.40/0.58      inference('clc', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X7 @ 
% 0.40/0.58             (k1_zfmisc_1 @ 
% 0.40/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.40/0.58          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.40/0.58          | ~ (v1_funct_1 @ X7)
% 0.40/0.58          | ~ (l1_struct_0 @ X9)
% 0.40/0.58          | ~ (l1_struct_0 @ X8)
% 0.40/0.58          | ~ (l1_struct_0 @ X10)
% 0.40/0.58          | (v1_funct_2 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.40/0.58             (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_2 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.58           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58          | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.58  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.58  thf('45', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('46', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('clc', [status(thm)], ['37', '38'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_2 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.58           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.40/0.58  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_1 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['10', '13', '23', '31', '39'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v1_funct_2 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.58           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58          (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.40/0.58      inference('clc', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X7 @ 
% 0.40/0.58             (k1_zfmisc_1 @ 
% 0.40/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))))
% 0.40/0.58          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X9))
% 0.40/0.58          | ~ (v1_funct_1 @ X7)
% 0.40/0.58          | ~ (l1_struct_0 @ X9)
% 0.40/0.58          | ~ (l1_struct_0 @ X8)
% 0.40/0.58          | ~ (l1_struct_0 @ X10)
% 0.40/0.58          | (m1_subset_1 @ (k2_tmap_1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.40/0.58             (k1_zfmisc_1 @ 
% 0.40/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.58           (k1_zfmisc_1 @ 
% 0.40/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.40/0.58             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.40/0.58          | ~ (l1_struct_0 @ X0)
% 0.40/0.58          | ~ (l1_struct_0 @ sk_A)
% 0.40/0.58          | ~ (l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.58  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.58  thf('57', plain, ((l1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('58', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.58        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.40/0.58      inference('clc', [status(thm)], ['37', '38'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ 
% 0.40/0.58           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.58           (k1_zfmisc_1 @ 
% 0.40/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.40/0.58             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.40/0.58          | ~ (l1_struct_0 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.40/0.58  thf(t49_tmap_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.58             ( l1_pre_topc @ B ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.40/0.58                 ( m1_subset_1 @
% 0.40/0.58                   C @ 
% 0.40/0.58                   ( k1_zfmisc_1 @
% 0.40/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.40/0.58               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.40/0.58                 ( ![D:$i]:
% 0.40/0.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.40/0.58                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X21)
% 0.40/0.58          | ~ (v2_pre_topc @ X21)
% 0.40/0.58          | ~ (l1_pre_topc @ X21)
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ X22 @ X21 @ X23) @ (u1_struct_0 @ X21))
% 0.40/0.58          | (v5_pre_topc @ X22 @ X21 @ X23)
% 0.40/0.58          | ~ (m1_subset_1 @ X22 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))))
% 0.40/0.58          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))
% 0.40/0.58          | ~ (v1_funct_1 @ X22)
% 0.40/0.58          | ~ (l1_pre_topc @ X23)
% 0.40/0.58          | ~ (v2_pre_topc @ X23)
% 0.40/0.58          | (v2_struct_0 @ X23))),
% 0.40/0.58      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_struct_0 @ X0)
% 0.40/0.58          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.58          | ~ (v1_funct_1 @ 
% 0.40/0.58               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.58          | ~ (v1_funct_2 @ 
% 0.40/0.58               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.58                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.58               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (m1_subset_1 @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.40/0.59             (u1_struct_0 @ X0))
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.59  thf('63', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X11)
% 0.40/0.59          | ~ (v2_pre_topc @ X11)
% 0.40/0.59          | (v2_struct_0 @ X11)
% 0.40/0.59          | ~ (m1_pre_topc @ X12 @ X11)
% 0.40/0.59          | (v2_pre_topc @ (k8_tmap_1 @ X11 @ X12)))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.40/0.59  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.40/0.59  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('70', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('71', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('72', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.59          | ~ (v1_funct_2 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (m1_subset_1 @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.40/0.59             (u1_struct_0 @ X0))
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '70', '71'])).
% 0.40/0.59  thf('73', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | (m1_subset_1 @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.40/0.59             (u1_struct_0 @ X0))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['52', '72'])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (m1_subset_1 @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.40/0.59             (u1_struct_0 @ X0))
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['73'])).
% 0.40/0.59  thf('75', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | ~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | (m1_subset_1 @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.40/0.59             (u1_struct_0 @ X0))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['51', '74'])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (m1_subset_1 @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 0.40/0.59             (u1_struct_0 @ X0))
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['75'])).
% 0.40/0.59  thf(t118_tmap_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.59               ( ( r1_tsep_1 @ B @ C ) =>
% 0.40/0.59                 ( ![D:$i]:
% 0.40/0.59                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.40/0.59                     ( r1_tmap_1 @
% 0.40/0.59                       C @ ( k8_tmap_1 @ A @ B ) @ 
% 0.40/0.59                       ( k2_tmap_1 @
% 0.40/0.59                         A @ ( k8_tmap_1 @ A @ B ) @ ( k9_tmap_1 @ A @ B ) @ C ) @ 
% 0.40/0.59                       D ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('77', plain,
% 0.40/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X17)
% 0.40/0.59          | ~ (m1_pre_topc @ X17 @ X18)
% 0.40/0.59          | ~ (r1_tsep_1 @ X17 @ X19)
% 0.40/0.59          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.40/0.59          | (r1_tmap_1 @ X19 @ (k8_tmap_1 @ X18 @ X17) @ 
% 0.40/0.59             (k2_tmap_1 @ X18 @ (k8_tmap_1 @ X18 @ X17) @ 
% 0.40/0.59              (k9_tmap_1 @ X18 @ X17) @ X19) @ 
% 0.40/0.59             X20)
% 0.40/0.59          | ~ (m1_pre_topc @ X19 @ X18)
% 0.40/0.59          | (v2_struct_0 @ X19)
% 0.40/0.59          | ~ (l1_pre_topc @ X18)
% 0.40/0.59          | ~ (v2_pre_topc @ X18)
% 0.40/0.59          | (v2_struct_0 @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [t118_tmap_1])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v2_struct_0 @ X1)
% 0.40/0.59          | ~ (v2_pre_topc @ X1)
% 0.40/0.59          | ~ (l1_pre_topc @ X1)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (m1_pre_topc @ X0 @ X1)
% 0.40/0.59          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ X1 @ X2) @ 
% 0.40/0.59             (k2_tmap_1 @ X1 @ (k8_tmap_1 @ X1 @ X2) @ (k9_tmap_1 @ X1 @ X2) @ 
% 0.40/0.59              X0) @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | ~ (r1_tsep_1 @ X2 @ X0)
% 0.40/0.59          | ~ (m1_pre_topc @ X2 @ X1)
% 0.40/0.59          | (v2_struct_0 @ X2))),
% 0.40/0.59      inference('sup-', [status(thm)], ['76', '77'])).
% 0.40/0.59  thf('79', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X2)
% 0.40/0.59          | ~ (m1_pre_topc @ X2 @ X1)
% 0.40/0.59          | ~ (r1_tsep_1 @ X2 @ X0)
% 0.40/0.59          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ X1 @ X2) @ 
% 0.40/0.59             (k2_tmap_1 @ X1 @ (k8_tmap_1 @ X1 @ X2) @ (k9_tmap_1 @ X1 @ X2) @ 
% 0.40/0.59              X0) @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | ~ (m1_pre_topc @ X0 @ X1)
% 0.40/0.59          | ~ (l1_pre_topc @ X1)
% 0.40/0.59          | ~ (v2_pre_topc @ X1)
% 0.40/0.59          | (v2_struct_0 @ X1)
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['78'])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.59          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.59          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.40/0.59          | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['50', '79'])).
% 0.40/0.59  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('83', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | (v2_struct_0 @ sk_A)
% 0.40/0.59          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.59          | (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             (sk_D @ 
% 0.40/0.59              (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59              X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | ~ (r1_tsep_1 @ sk_B @ X0)
% 0.40/0.59          | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.40/0.59  thf('84', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 0.40/0.59        | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           (sk_D @ 
% 0.40/0.59            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59            sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_C)
% 0.40/0.59        | ~ (v2_pre_topc @ sk_C)
% 0.40/0.59        | (v2_struct_0 @ sk_C)
% 0.40/0.59        | ~ (l1_struct_0 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['49', '83'])).
% 0.40/0.59  thf('85', plain, ((r1_tsep_1 @ sk_B @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('86', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_m1_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.40/0.59  thf('87', plain,
% 0.40/0.59      (![X3 : $i, X4 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.40/0.59  thf('88', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['86', '87'])).
% 0.40/0.59  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('90', plain, ((l1_pre_topc @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['88', '89'])).
% 0.40/0.59  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc1_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.40/0.59  thf('92', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (m1_pre_topc @ X0 @ X1)
% 0.40/0.59          | (v2_pre_topc @ X0)
% 0.40/0.59          | ~ (l1_pre_topc @ X1)
% 0.40/0.59          | ~ (v2_pre_topc @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.40/0.59  thf('93', plain,
% 0.40/0.59      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['91', '92'])).
% 0.40/0.59  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('96', plain, ((v2_pre_topc @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.40/0.59  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['88', '89'])).
% 0.40/0.59  thf('98', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.59  thf('99', plain, ((l1_struct_0 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('100', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | (r1_tmap_1 @ sk_C @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           (sk_D @ 
% 0.40/0.59            (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59            sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['84', '85', '90', '96', '99'])).
% 0.40/0.59  thf('101', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((m1_subset_1 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59           (k1_zfmisc_1 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.40/0.59             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.40/0.59  thf('102', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X21)
% 0.40/0.59          | ~ (v2_pre_topc @ X21)
% 0.40/0.59          | ~ (l1_pre_topc @ X21)
% 0.40/0.59          | ~ (r1_tmap_1 @ X21 @ X23 @ X22 @ (sk_D @ X22 @ X21 @ X23))
% 0.40/0.59          | (v5_pre_topc @ X22 @ X21 @ X23)
% 0.40/0.59          | ~ (m1_subset_1 @ X22 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))))
% 0.40/0.59          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X23))
% 0.40/0.59          | ~ (v1_funct_1 @ X22)
% 0.40/0.59          | ~ (l1_pre_topc @ X23)
% 0.40/0.59          | ~ (v2_pre_topc @ X23)
% 0.40/0.59          | (v2_struct_0 @ X23))),
% 0.40/0.59      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.40/0.59  thf('103', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.59          | ~ (v1_funct_2 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59               (sk_D @ 
% 0.40/0.59                (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                 (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59                X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['101', '102'])).
% 0.40/0.59  thf('104', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['68', '69'])).
% 0.40/0.59  thf('105', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('106', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X0)
% 0.40/0.59          | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (v1_funct_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.59          | ~ (v1_funct_2 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59               (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59             X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59          | ~ (r1_tmap_1 @ X0 @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59               (sk_D @ 
% 0.40/0.59                (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                 (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59                X0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | ~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v2_pre_topc @ X0)
% 0.40/0.59          | (v2_struct_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.40/0.59  thf('107', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_C)
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_C)
% 0.40/0.59        | ~ (v2_pre_topc @ sk_C)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_C)
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C))
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['100', '106'])).
% 0.40/0.59  thf('108', plain, ((v2_pre_topc @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.40/0.59  thf('109', plain, ((l1_pre_topc @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['88', '89'])).
% 0.40/0.59  thf('110', plain, ((l1_struct_0 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('111', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_C)
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_C)
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C))
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.40/0.59  thf('112', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59        | (v2_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['111'])).
% 0.40/0.59  thf('113', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_C)
% 0.40/0.59        | (v2_struct_0 @ sk_C)
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_B)
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['48', '112'])).
% 0.40/0.59  thf('114', plain, ((l1_struct_0 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('115', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_C)
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_B)
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['113', '114'])).
% 0.40/0.59  thf('116', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_C)
% 0.40/0.59        | (v2_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['40', '115'])).
% 0.40/0.59  thf('117', plain, ((l1_struct_0 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('118', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['116', '117'])).
% 0.40/0.59  thf('119', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59             sk_C @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | ~ (m1_subset_1 @ 
% 0.40/0.59             (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59              (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59             (k1_zfmisc_1 @ 
% 0.40/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('120', plain,
% 0.40/0.59      ((~ (v5_pre_topc @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59         <= (~
% 0.40/0.59             ((v5_pre_topc @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59               sk_C @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.40/0.59      inference('split', [status(esa)], ['119'])).
% 0.40/0.59  thf('121', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((m1_subset_1 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59           (k1_zfmisc_1 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 0.40/0.59             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.40/0.59  thf('122', plain,
% 0.40/0.59      ((~ (m1_subset_1 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           (k1_zfmisc_1 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.40/0.59      inference('split', [status(esa)], ['119'])).
% 0.40/0.59  thf('123', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_C))
% 0.40/0.59         <= (~
% 0.40/0.59             ((m1_subset_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['121', '122'])).
% 0.40/0.59  thf('124', plain, ((l1_struct_0 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('125', plain,
% 0.40/0.59      (((m1_subset_1 @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59         (k1_zfmisc_1 @ 
% 0.40/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.40/0.59      inference('demod', [status(thm)], ['123', '124'])).
% 0.40/0.59  thf('126', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_funct_2 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ X0) @ 
% 0.40/0.59           (u1_struct_0 @ X0) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.40/0.59  thf('127', plain,
% 0.40/0.59      ((~ (v1_funct_2 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.40/0.59         <= (~
% 0.40/0.59             ((v1_funct_2 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.40/0.59      inference('split', [status(esa)], ['119'])).
% 0.40/0.59  thf('128', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_C))
% 0.40/0.59         <= (~
% 0.40/0.59             ((v1_funct_2 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['126', '127'])).
% 0.40/0.59  thf('129', plain, ((l1_struct_0 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('130', plain,
% 0.40/0.59      (((v1_funct_2 @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.40/0.59      inference('demod', [status(thm)], ['128', '129'])).
% 0.40/0.59  thf('131', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_funct_1 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ X0))
% 0.40/0.59          | ~ (l1_struct_0 @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['10', '13', '23', '31', '39'])).
% 0.40/0.59  thf('132', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ 
% 0.40/0.59           (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59            (k9_tmap_1 @ sk_A @ sk_B) @ sk_C)))
% 0.40/0.59         <= (~
% 0.40/0.59             ((v1_funct_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ sk_C))))),
% 0.40/0.59      inference('split', [status(esa)], ['119'])).
% 0.40/0.59  thf('133', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_C))
% 0.40/0.59         <= (~
% 0.40/0.59             ((v1_funct_1 @ 
% 0.40/0.59               (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59                (k9_tmap_1 @ sk_A @ sk_B) @ sk_C))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['131', '132'])).
% 0.40/0.59  thf('134', plain, ((l1_struct_0 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['97', '98'])).
% 0.40/0.59  thf('135', plain,
% 0.40/0.59      (((v1_funct_1 @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['133', '134'])).
% 0.40/0.59  thf('136', plain,
% 0.40/0.59      (~
% 0.40/0.59       ((v5_pre_topc @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59         sk_C @ (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.40/0.59       ~
% 0.40/0.59       ((v1_funct_1 @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C))) | 
% 0.40/0.59       ~
% 0.40/0.59       ((v1_funct_2 @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) | 
% 0.40/0.59       ~
% 0.40/0.59       ((m1_subset_1 @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59         (k1_zfmisc_1 @ 
% 0.40/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 0.40/0.59           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.40/0.59      inference('split', [status(esa)], ['119'])).
% 0.40/0.59  thf('137', plain,
% 0.40/0.59      (~
% 0.40/0.59       ((v5_pre_topc @ 
% 0.40/0.59         (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59          (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59         sk_C @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.40/0.59      inference('sat_resolution*', [status(thm)], ['125', '130', '135', '136'])).
% 0.40/0.59  thf('138', plain,
% 0.40/0.59      (~ (v5_pre_topc @ 
% 0.40/0.59          (k2_tmap_1 @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B) @ 
% 0.40/0.59           (k9_tmap_1 @ sk_A @ sk_B) @ sk_C) @ 
% 0.40/0.59          sk_C @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('simpl_trail', [status(thm)], ['120', '137'])).
% 0.40/0.59  thf('139', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_C)
% 0.40/0.59        | (v2_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['118', '138'])).
% 0.40/0.59  thf(fc5_tmap_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.59         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.40/0.59       ( ( ~( v2_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.40/0.59         ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.40/0.59         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.40/0.59  thf('140', plain,
% 0.40/0.59      (![X15 : $i, X16 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X15)
% 0.40/0.59          | ~ (v2_pre_topc @ X15)
% 0.40/0.59          | (v2_struct_0 @ X15)
% 0.40/0.59          | ~ (m1_pre_topc @ X16 @ X15)
% 0.40/0.59          | ~ (v2_struct_0 @ (k8_tmap_1 @ X15 @ X16)))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc5_tmap_1])).
% 0.40/0.59  thf('141', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_C)
% 0.40/0.59        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['139', '140'])).
% 0.40/0.59  thf('142', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('145', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_A)
% 0.40/0.59        | (v2_struct_0 @ sk_C)
% 0.40/0.59        | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.40/0.59  thf('146', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('simplify', [status(thm)], ['145'])).
% 0.40/0.59  thf('147', plain, (~ (v2_struct_0 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('148', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.40/0.59      inference('clc', [status(thm)], ['146', '147'])).
% 0.40/0.59  thf('149', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('150', plain, ((v2_struct_0 @ sk_A)),
% 0.40/0.59      inference('clc', [status(thm)], ['148', '149'])).
% 0.40/0.59  thf('151', plain, ($false), inference('demod', [status(thm)], ['0', '150'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.43/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
