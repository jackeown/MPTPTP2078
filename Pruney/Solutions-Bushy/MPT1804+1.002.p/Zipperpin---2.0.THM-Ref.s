%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1804+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.761Hqlpdle

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:18 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  206 (1163 expanded)
%              Number of leaves         :   35 ( 351 expanded)
%              Depth                    :   33
%              Number of atoms          : 3243 (44601 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X17 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d4_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( ( k2_tmap_1 @ X4 @ X2 @ X5 @ X3 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X2 ) @ X5 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('16',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X16 @ X17 ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('24',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('32',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('40',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','21','29','37','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X7 @ X8 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

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

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_struct_0 @ X12 )
      | ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X11 @ X12 @ X10 @ X13 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('60',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('63',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('66',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','64','65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tsep_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','64','65','66'])).

thf('72',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('73',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_struct_0 @ X12 )
      | ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X13 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X11 @ X12 @ X10 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('76',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('77',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('78',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

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

thf('80',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( m1_subset_1 @ ( sk_D @ X28 @ X27 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ( v5_pre_topc @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('81',plain,(
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
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('83',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('84',plain,(
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
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
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
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','86'])).

thf('88',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('89',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('94',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('97',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('102',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','94','100','101'])).

thf('103',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

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

thf('104',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( r1_tsep_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( r1_tmap_1 @ X25 @ ( k8_tmap_1 @ X24 @ X23 ) @ ( k2_tmap_1 @ X24 @ ( k8_tmap_1 @ X24 @ X23 ) @ ( k9_tmap_1 @ X24 @ X23 ) @ X25 ) @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t118_tmap_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ X0 @ X1 ) @ ( k2_tmap_1 @ X0 @ ( k8_tmap_1 @ X0 @ X1 ) @ ( k9_tmap_1 @ X0 @ X1 ) @ sk_C ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( r1_tsep_1 @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( r1_tsep_1 @ X1 @ sk_C )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ X0 @ X1 ) @ ( k2_tmap_1 @ X0 @ ( k8_tmap_1 @ X0 @ X1 ) @ ( k9_tmap_1 @ X0 @ X1 ) @ sk_C ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ X0 @ sk_B ) @ ( k2_tmap_1 @ X0 @ ( k8_tmap_1 @ X0 @ sk_B ) @ ( k9_tmap_1 @ X0 @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('114',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( r1_tmap_1 @ X27 @ X29 @ X28 @ ( sk_D @ X28 @ X27 @ X29 ) )
      | ( v5_pre_topc @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('115',plain,(
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
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('117',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('118',plain,(
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
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('121',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('122',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['92','93'])).

thf('123',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['92','93'])).

thf('127',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('133',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['130'])).

thf('134',plain,
    ( ~ ( l1_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['92','93'])).

thf('136',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('138',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_struct_0 @ X12 )
      | ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X11 @ X12 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('141',plain,(
    l1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('142',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('143',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(split,[status(esa)],['130'])).

thf('146',plain,
    ( ~ ( l1_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['92','93'])).

thf('148',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','64','65','66'])).

thf('150',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['130'])).

thf('151',plain,
    ( ~ ( l1_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['92','93'])).

thf('153',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['130'])).

thf('155',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['136','148','153','154'])).

thf('156',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_C ) @ sk_C @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['131','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','156'])).

thf(fc5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ~ ( v2_struct_0 @ ( k8_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('158',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( v2_struct_0 @ ( k8_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_tmap_1])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    $false ),
    inference(demod,[status(thm)],['0','168'])).


%------------------------------------------------------------------------------
