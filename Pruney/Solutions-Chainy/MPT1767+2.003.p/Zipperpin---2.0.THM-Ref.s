%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coo7xSsjeg

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:07 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 933 expanded)
%              Number of leaves         :   26 ( 282 expanded)
%              Depth                    :   24
%              Number of atoms          : 2308 (34487 expanded)
%              Number of equality atoms :   25 ( 128 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t78_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

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
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 )
      | ( X0 != X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['24','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X11 )
      | ( ( k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) @ X12 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ( ( k2_tmap_1 @ X6 @ X4 @ X7 @ X5 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74','75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('85',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('86',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','83','84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','101'])).

thf('103',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('104',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['86','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('111',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('112',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf(t77_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ ( k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X22 ) @ ( k2_tmap_1 @ X21 @ X19 @ X24 @ X20 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) @ X22 @ ( k2_tmap_1 @ X21 @ X19 @ X24 @ X23 ) )
      | ~ ( m1_pre_topc @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('116',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('117',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['66','82'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','129'])).

thf('131',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['0','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coo7xSsjeg
% 0.15/0.38  % Computer   : n018.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 15:16:42 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.24/0.38  % Number of cores: 8
% 0.24/0.38  % Python version: Python 3.6.8
% 0.24/0.39  % Running in FO mode
% 0.25/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.76  % Solved by: fo/fo7.sh
% 0.25/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.76  % done 436 iterations in 0.267s
% 0.25/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.76  % SZS output start Refutation
% 0.25/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.25/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.76  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.25/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.76  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.25/0.76  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.25/0.76  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.25/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.76  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.25/0.76  thf(sk_E_type, type, sk_E: $i).
% 0.25/0.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.76  thf(t78_tmap_1, conjecture,
% 0.25/0.76    (![A:$i]:
% 0.25/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.76       ( ![B:$i]:
% 0.25/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.76             ( l1_pre_topc @ B ) ) =>
% 0.25/0.76           ( ![C:$i]:
% 0.25/0.76             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.25/0.76               ( ![D:$i]:
% 0.25/0.76                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.25/0.76                   ( ![E:$i]:
% 0.25/0.76                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.76                         ( v1_funct_2 @
% 0.25/0.76                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.76                         ( m1_subset_1 @
% 0.25/0.76                           E @ 
% 0.25/0.76                           ( k1_zfmisc_1 @
% 0.25/0.76                             ( k2_zfmisc_1 @
% 0.25/0.76                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.76                       ( ( m1_pre_topc @ C @ D ) =>
% 0.25/0.76                         ( r2_funct_2 @
% 0.25/0.76                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.25/0.76                           ( k3_tmap_1 @
% 0.25/0.76                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.25/0.76                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.76    (~( ![A:$i]:
% 0.25/0.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.76            ( l1_pre_topc @ A ) ) =>
% 0.25/0.76          ( ![B:$i]:
% 0.25/0.76            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.76                ( l1_pre_topc @ B ) ) =>
% 0.25/0.76              ( ![C:$i]:
% 0.25/0.76                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.25/0.76                  ( ![D:$i]:
% 0.25/0.76                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.25/0.76                      ( ![E:$i]:
% 0.25/0.76                        ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.76                            ( v1_funct_2 @
% 0.25/0.76                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.76                            ( m1_subset_1 @
% 0.25/0.76                              E @ 
% 0.25/0.76                              ( k1_zfmisc_1 @
% 0.25/0.76                                ( k2_zfmisc_1 @
% 0.25/0.76                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.76                          ( ( m1_pre_topc @ C @ D ) =>
% 0.25/0.76                            ( r2_funct_2 @
% 0.25/0.76                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.25/0.76                              ( k3_tmap_1 @
% 0.25/0.76                                A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.25/0.76                              ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.76    inference('cnf.neg', [status(esa)], [t78_tmap_1])).
% 0.25/0.76  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf(t2_tsep_1, axiom,
% 0.25/0.76    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.25/0.76  thf('3', plain,
% 0.25/0.76      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.25/0.76      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.25/0.76  thf('4', plain,
% 0.25/0.76      ((m1_subset_1 @ sk_E @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf(dt_k3_tmap_1, axiom,
% 0.25/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.25/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.76         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.25/0.76         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.25/0.76         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.25/0.76         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.76         ( m1_subset_1 @
% 0.25/0.76           E @ 
% 0.25/0.76           ( k1_zfmisc_1 @
% 0.25/0.76             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.76       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.25/0.76         ( v1_funct_2 @
% 0.25/0.76           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.25/0.76           ( u1_struct_0 @ B ) ) & 
% 0.25/0.76         ( m1_subset_1 @
% 0.25/0.76           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.25/0.76           ( k1_zfmisc_1 @
% 0.25/0.76             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.25/0.76  thf('5', plain,
% 0.25/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.25/0.76         (~ (m1_pre_topc @ X13 @ X14)
% 0.25/0.76          | ~ (m1_pre_topc @ X15 @ X14)
% 0.25/0.76          | ~ (l1_pre_topc @ X16)
% 0.25/0.76          | ~ (v2_pre_topc @ X16)
% 0.25/0.76          | (v2_struct_0 @ X16)
% 0.25/0.76          | ~ (l1_pre_topc @ X14)
% 0.25/0.76          | ~ (v2_pre_topc @ X14)
% 0.25/0.76          | (v2_struct_0 @ X14)
% 0.25/0.76          | ~ (v1_funct_1 @ X17)
% 0.25/0.76          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.25/0.76          | ~ (m1_subset_1 @ X17 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.25/0.76          | (m1_subset_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.25/0.76             (k1_zfmisc_1 @ 
% 0.25/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))))),
% 0.25/0.76      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.25/0.76  thf('6', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76           (k1_zfmisc_1 @ 
% 0.25/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.25/0.76          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.76          | (v2_struct_0 @ X1)
% 0.25/0.76          | ~ (v2_pre_topc @ X1)
% 0.25/0.76          | ~ (l1_pre_topc @ X1)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.25/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.76  thf('7', plain,
% 0.25/0.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('11', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76           (k1_zfmisc_1 @ 
% 0.25/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.25/0.76          | (v2_struct_0 @ X1)
% 0.25/0.76          | ~ (v2_pre_topc @ X1)
% 0.25/0.76          | ~ (l1_pre_topc @ X1)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.25/0.76      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.25/0.76  thf('12', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         (~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_A)
% 0.25/0.76          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76             (k1_zfmisc_1 @ 
% 0.25/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.25/0.76      inference('sup-', [status(thm)], ['3', '11'])).
% 0.25/0.76  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('16', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ sk_A)
% 0.25/0.76          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76             (k1_zfmisc_1 @ 
% 0.25/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.25/0.76      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.25/0.76  thf('17', plain,
% 0.25/0.76      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76         (k1_zfmisc_1 @ 
% 0.25/0.76          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.25/0.76        | (v2_struct_0 @ sk_A)
% 0.25/0.76        | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('sup-', [status(thm)], ['2', '16'])).
% 0.25/0.76  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('19', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_B)
% 0.25/0.76        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76           (k1_zfmisc_1 @ 
% 0.25/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.25/0.76      inference('clc', [status(thm)], ['17', '18'])).
% 0.25/0.76  thf('20', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('21', plain,
% 0.25/0.76      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('clc', [status(thm)], ['19', '20'])).
% 0.25/0.76  thf(redefinition_r2_funct_2, axiom,
% 0.25/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.25/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.25/0.76         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.25/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.25/0.76       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.25/0.76  thf('22', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.25/0.76          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.25/0.76          | ~ (v1_funct_1 @ X0)
% 0.25/0.76          | ~ (v1_funct_1 @ X3)
% 0.25/0.76          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.25/0.76          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.25/0.76          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 0.25/0.76          | ((X0) != (X3)))),
% 0.25/0.76      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.25/0.76  thf('23', plain,
% 0.25/0.76      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.76         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 0.25/0.76          | ~ (v1_funct_1 @ X3)
% 0.25/0.76          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.25/0.76          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.25/0.76      inference('simplify', [status(thm)], ['22'])).
% 0.25/0.76  thf('24', plain,
% 0.25/0.76      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.25/0.76        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.25/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.25/0.76      inference('sup-', [status(thm)], ['21', '23'])).
% 0.25/0.76  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('26', plain,
% 0.25/0.76      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.25/0.76      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.25/0.76  thf('27', plain,
% 0.25/0.76      ((m1_subset_1 @ sk_E @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('28', plain,
% 0.25/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.25/0.76         (~ (m1_pre_topc @ X13 @ X14)
% 0.25/0.76          | ~ (m1_pre_topc @ X15 @ X14)
% 0.25/0.76          | ~ (l1_pre_topc @ X16)
% 0.25/0.76          | ~ (v2_pre_topc @ X16)
% 0.25/0.76          | (v2_struct_0 @ X16)
% 0.25/0.76          | ~ (l1_pre_topc @ X14)
% 0.25/0.76          | ~ (v2_pre_topc @ X14)
% 0.25/0.76          | (v2_struct_0 @ X14)
% 0.25/0.76          | ~ (v1_funct_1 @ X17)
% 0.25/0.76          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.25/0.76          | ~ (m1_subset_1 @ X17 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.25/0.76          | (v1_funct_1 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17)))),
% 0.25/0.76      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.25/0.76  thf('29', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.25/0.76          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.76          | (v2_struct_0 @ X1)
% 0.25/0.76          | ~ (v2_pre_topc @ X1)
% 0.25/0.76          | ~ (l1_pre_topc @ X1)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.25/0.76      inference('sup-', [status(thm)], ['27', '28'])).
% 0.25/0.76  thf('30', plain,
% 0.25/0.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('31', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('32', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('34', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.25/0.76          | (v2_struct_0 @ X1)
% 0.25/0.76          | ~ (v2_pre_topc @ X1)
% 0.25/0.76          | ~ (l1_pre_topc @ X1)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.25/0.76      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.25/0.76  thf('35', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         (~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_A)
% 0.25/0.76          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.25/0.76      inference('sup-', [status(thm)], ['26', '34'])).
% 0.25/0.76  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('39', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ sk_A)
% 0.25/0.76          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.25/0.76      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.25/0.76  thf('40', plain,
% 0.25/0.76      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.25/0.76        | (v2_struct_0 @ sk_A)
% 0.25/0.76        | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('sup-', [status(thm)], ['25', '39'])).
% 0.25/0.76  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('42', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_B)
% 0.25/0.76        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.25/0.76      inference('clc', [status(thm)], ['40', '41'])).
% 0.25/0.76  thf('43', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('44', plain,
% 0.25/0.76      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('clc', [status(thm)], ['42', '43'])).
% 0.25/0.76  thf('45', plain,
% 0.25/0.76      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.25/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.25/0.76      inference('demod', [status(thm)], ['24', '44'])).
% 0.25/0.76  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('47', plain,
% 0.25/0.76      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.25/0.76      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.25/0.76  thf('48', plain,
% 0.25/0.76      ((m1_subset_1 @ sk_E @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf(d5_tmap_1, axiom,
% 0.25/0.76    (![A:$i]:
% 0.25/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.76       ( ![B:$i]:
% 0.25/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.76             ( l1_pre_topc @ B ) ) =>
% 0.25/0.76           ( ![C:$i]:
% 0.25/0.76             ( ( m1_pre_topc @ C @ A ) =>
% 0.25/0.76               ( ![D:$i]:
% 0.25/0.76                 ( ( m1_pre_topc @ D @ A ) =>
% 0.25/0.76                   ( ![E:$i]:
% 0.25/0.76                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.76                         ( v1_funct_2 @
% 0.25/0.76                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.76                         ( m1_subset_1 @
% 0.25/0.76                           E @ 
% 0.25/0.76                           ( k1_zfmisc_1 @
% 0.25/0.76                             ( k2_zfmisc_1 @
% 0.25/0.76                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.76                       ( ( m1_pre_topc @ D @ C ) =>
% 0.25/0.76                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.25/0.76                           ( k2_partfun1 @
% 0.25/0.76                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.25/0.76                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.76  thf('49', plain,
% 0.25/0.76      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.25/0.76         ((v2_struct_0 @ X8)
% 0.25/0.76          | ~ (v2_pre_topc @ X8)
% 0.25/0.76          | ~ (l1_pre_topc @ X8)
% 0.25/0.76          | ~ (m1_pre_topc @ X9 @ X10)
% 0.25/0.76          | ~ (m1_pre_topc @ X9 @ X11)
% 0.25/0.76          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.25/0.76                 X12 @ (u1_struct_0 @ X9)))
% 0.25/0.76          | ~ (m1_subset_1 @ X12 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.25/0.76          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.25/0.76          | ~ (v1_funct_1 @ X12)
% 0.25/0.76          | ~ (m1_pre_topc @ X11 @ X10)
% 0.25/0.76          | ~ (l1_pre_topc @ X10)
% 0.25/0.76          | ~ (v2_pre_topc @ X10)
% 0.25/0.76          | (v2_struct_0 @ X10))),
% 0.25/0.76      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.25/0.76  thf('50', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((v2_struct_0 @ X0)
% 0.25/0.76          | ~ (v2_pre_topc @ X0)
% 0.25/0.76          | ~ (l1_pre_topc @ X0)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.25/0.76          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.76          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76                 sk_E @ (u1_struct_0 @ X1)))
% 0.25/0.76          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.25/0.76          | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('sup-', [status(thm)], ['48', '49'])).
% 0.25/0.76  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('52', plain,
% 0.25/0.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('55', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((v2_struct_0 @ X0)
% 0.25/0.76          | ~ (v2_pre_topc @ X0)
% 0.25/0.76          | ~ (l1_pre_topc @ X0)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.25/0.76          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76                 sk_E @ (u1_struct_0 @ X1)))
% 0.25/0.76          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.25/0.76          | ~ (m1_pre_topc @ X1 @ X0)
% 0.25/0.76          | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.25/0.76  thf('56', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         (~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_A))),
% 0.25/0.76      inference('sup-', [status(thm)], ['47', '55'])).
% 0.25/0.76  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('60', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         ((v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.76          | (v2_struct_0 @ sk_A))),
% 0.25/0.76      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.25/0.76  thf('61', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         ((v2_struct_0 @ sk_A)
% 0.25/0.76          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('simplify', [status(thm)], ['60'])).
% 0.25/0.76  thf('62', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_B)
% 0.25/0.76        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.25/0.76            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76               sk_E @ (u1_struct_0 @ sk_D)))
% 0.25/0.76        | (v2_struct_0 @ sk_A))),
% 0.25/0.76      inference('sup-', [status(thm)], ['46', '61'])).
% 0.25/0.76  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('64', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_A)
% 0.25/0.76        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.25/0.76            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.25/0.76      inference('clc', [status(thm)], ['62', '63'])).
% 0.25/0.76  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('66', plain,
% 0.25/0.76      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.25/0.76         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.25/0.76            (u1_struct_0 @ sk_D)))),
% 0.25/0.76      inference('clc', [status(thm)], ['64', '65'])).
% 0.25/0.76  thf('67', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('68', plain,
% 0.25/0.76      ((m1_subset_1 @ sk_E @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf(d4_tmap_1, axiom,
% 0.25/0.76    (![A:$i]:
% 0.25/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.76       ( ![B:$i]:
% 0.25/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.76             ( l1_pre_topc @ B ) ) =>
% 0.25/0.76           ( ![C:$i]:
% 0.25/0.76             ( ( ( v1_funct_1 @ C ) & 
% 0.25/0.76                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.76                 ( m1_subset_1 @
% 0.25/0.76                   C @ 
% 0.25/0.76                   ( k1_zfmisc_1 @
% 0.25/0.76                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.76               ( ![D:$i]:
% 0.25/0.76                 ( ( m1_pre_topc @ D @ A ) =>
% 0.25/0.76                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.25/0.76                     ( k2_partfun1 @
% 0.25/0.76                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.25/0.76                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.76  thf('69', plain,
% 0.25/0.76      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.76         ((v2_struct_0 @ X4)
% 0.25/0.76          | ~ (v2_pre_topc @ X4)
% 0.25/0.76          | ~ (l1_pre_topc @ X4)
% 0.25/0.76          | ~ (m1_pre_topc @ X5 @ X6)
% 0.25/0.76          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.25/0.76                 (u1_struct_0 @ X5)))
% 0.25/0.76          | ~ (m1_subset_1 @ X7 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.25/0.76          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.25/0.76          | ~ (v1_funct_1 @ X7)
% 0.25/0.76          | ~ (l1_pre_topc @ X6)
% 0.25/0.76          | ~ (v2_pre_topc @ X6)
% 0.25/0.76          | (v2_struct_0 @ X6))),
% 0.25/0.76      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.25/0.76  thf('70', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         ((v2_struct_0 @ sk_A)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.76          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('sup-', [status(thm)], ['68', '69'])).
% 0.25/0.76  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('74', plain,
% 0.25/0.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('77', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         ((v2_struct_0 @ sk_A)
% 0.25/0.76          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.25/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76                 sk_E @ (u1_struct_0 @ X0)))
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('demod', [status(thm)],
% 0.25/0.76                ['70', '71', '72', '73', '74', '75', '76'])).
% 0.25/0.76  thf('78', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_B)
% 0.25/0.76        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76               sk_E @ (u1_struct_0 @ sk_D)))
% 0.25/0.76        | (v2_struct_0 @ sk_A))),
% 0.25/0.76      inference('sup-', [status(thm)], ['67', '77'])).
% 0.25/0.76  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('80', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_A)
% 0.25/0.76        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.25/0.76      inference('clc', [status(thm)], ['78', '79'])).
% 0.25/0.76  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('82', plain,
% 0.25/0.76      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.25/0.76            (u1_struct_0 @ sk_D)))),
% 0.25/0.76      inference('clc', [status(thm)], ['80', '81'])).
% 0.25/0.76  thf('83', plain,
% 0.25/0.76      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('sup+', [status(thm)], ['66', '82'])).
% 0.25/0.76  thf('84', plain,
% 0.25/0.76      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('sup+', [status(thm)], ['66', '82'])).
% 0.25/0.76  thf('85', plain,
% 0.25/0.76      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('sup+', [status(thm)], ['66', '82'])).
% 0.25/0.76  thf('86', plain,
% 0.25/0.76      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.25/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.25/0.76      inference('demod', [status(thm)], ['45', '83', '84', '85'])).
% 0.25/0.76  thf('87', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('88', plain,
% 0.25/0.76      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.25/0.76      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.25/0.76  thf('89', plain,
% 0.25/0.76      ((m1_subset_1 @ sk_E @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('90', plain,
% 0.25/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.25/0.76         (~ (m1_pre_topc @ X13 @ X14)
% 0.25/0.76          | ~ (m1_pre_topc @ X15 @ X14)
% 0.25/0.76          | ~ (l1_pre_topc @ X16)
% 0.25/0.76          | ~ (v2_pre_topc @ X16)
% 0.25/0.76          | (v2_struct_0 @ X16)
% 0.25/0.76          | ~ (l1_pre_topc @ X14)
% 0.25/0.76          | ~ (v2_pre_topc @ X14)
% 0.25/0.76          | (v2_struct_0 @ X14)
% 0.25/0.76          | ~ (v1_funct_1 @ X17)
% 0.25/0.76          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.25/0.76          | ~ (m1_subset_1 @ X17 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))))
% 0.25/0.76          | (v1_funct_2 @ (k3_tmap_1 @ X14 @ X16 @ X15 @ X13 @ X17) @ 
% 0.25/0.76             (u1_struct_0 @ X13) @ (u1_struct_0 @ X16)))),
% 0.25/0.76      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.25/0.76  thf('91', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.76          | (v2_struct_0 @ X1)
% 0.25/0.76          | ~ (v2_pre_topc @ X1)
% 0.25/0.76          | ~ (l1_pre_topc @ X1)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.25/0.76      inference('sup-', [status(thm)], ['89', '90'])).
% 0.25/0.76  thf('92', plain,
% 0.25/0.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('93', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('96', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i]:
% 0.25/0.76         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | (v2_struct_0 @ X1)
% 0.25/0.76          | ~ (v2_pre_topc @ X1)
% 0.25/0.76          | ~ (l1_pre_topc @ X1)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.25/0.76      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.25/0.76  thf('97', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         (~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_A)
% 0.25/0.76          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.25/0.76      inference('sup-', [status(thm)], ['88', '96'])).
% 0.25/0.76  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('101', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ sk_A)
% 0.25/0.76          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.25/0.76             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.25/0.76      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.25/0.76  thf('102', plain,
% 0.25/0.76      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.25/0.76        | (v2_struct_0 @ sk_A)
% 0.25/0.76        | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('sup-', [status(thm)], ['87', '101'])).
% 0.25/0.76  thf('103', plain,
% 0.25/0.76      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('sup+', [status(thm)], ['66', '82'])).
% 0.25/0.76  thf('104', plain,
% 0.25/0.76      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.25/0.76        | (v2_struct_0 @ sk_A)
% 0.25/0.76        | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('demod', [status(thm)], ['102', '103'])).
% 0.25/0.76  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('106', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_B)
% 0.25/0.76        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.25/0.76      inference('clc', [status(thm)], ['104', '105'])).
% 0.25/0.76  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('108', plain,
% 0.25/0.76      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('clc', [status(thm)], ['106', '107'])).
% 0.25/0.76  thf('109', plain,
% 0.25/0.76      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76        (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76        (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.25/0.76      inference('demod', [status(thm)], ['86', '108'])).
% 0.25/0.76  thf('110', plain,
% 0.25/0.76      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('clc', [status(thm)], ['19', '20'])).
% 0.25/0.76  thf('111', plain,
% 0.25/0.76      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('sup+', [status(thm)], ['66', '82'])).
% 0.25/0.76  thf('112', plain,
% 0.25/0.76      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('demod', [status(thm)], ['110', '111'])).
% 0.25/0.76  thf(t77_tmap_1, axiom,
% 0.25/0.76    (![A:$i]:
% 0.25/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.76       ( ![B:$i]:
% 0.25/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.25/0.76             ( l1_pre_topc @ B ) ) =>
% 0.25/0.76           ( ![C:$i]:
% 0.25/0.76             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.25/0.76               ( ![D:$i]:
% 0.25/0.76                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.25/0.76                   ( ![E:$i]:
% 0.25/0.76                     ( ( ( v1_funct_1 @ E ) & 
% 0.25/0.76                         ( v1_funct_2 @
% 0.25/0.76                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.76                         ( m1_subset_1 @
% 0.25/0.76                           E @ 
% 0.25/0.76                           ( k1_zfmisc_1 @
% 0.25/0.76                             ( k2_zfmisc_1 @
% 0.25/0.76                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.76                       ( ![F:$i]:
% 0.25/0.76                         ( ( ( v1_funct_1 @ F ) & 
% 0.25/0.76                             ( v1_funct_2 @
% 0.25/0.76                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.25/0.76                             ( m1_subset_1 @
% 0.25/0.76                               F @ 
% 0.25/0.76                               ( k1_zfmisc_1 @
% 0.25/0.76                                 ( k2_zfmisc_1 @
% 0.25/0.76                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.25/0.76                           ( ( ( r2_funct_2 @
% 0.25/0.76                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.25/0.76                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.25/0.76                               ( m1_pre_topc @ D @ C ) ) =>
% 0.25/0.76                             ( r2_funct_2 @
% 0.25/0.76                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.25/0.76                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.25/0.76                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.76  thf('113', plain,
% 0.25/0.76      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.25/0.76         ((v2_struct_0 @ X19)
% 0.25/0.76          | ~ (v2_pre_topc @ X19)
% 0.25/0.76          | ~ (l1_pre_topc @ X19)
% 0.25/0.76          | (v2_struct_0 @ X20)
% 0.25/0.76          | ~ (m1_pre_topc @ X20 @ X21)
% 0.25/0.76          | ~ (v1_funct_1 @ X22)
% 0.25/0.76          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))
% 0.25/0.76          | ~ (m1_subset_1 @ X22 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))))
% 0.25/0.76          | (r2_funct_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ 
% 0.25/0.76             (k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X22) @ 
% 0.25/0.76             (k2_tmap_1 @ X21 @ X19 @ X24 @ X20))
% 0.25/0.76          | ~ (r2_funct_2 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19) @ X22 @ 
% 0.25/0.76               (k2_tmap_1 @ X21 @ X19 @ X24 @ X23))
% 0.25/0.76          | ~ (m1_pre_topc @ X20 @ X23)
% 0.25/0.76          | ~ (m1_subset_1 @ X24 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.25/0.76          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.25/0.76          | ~ (v1_funct_1 @ X24)
% 0.25/0.76          | ~ (m1_pre_topc @ X23 @ X21)
% 0.25/0.76          | (v2_struct_0 @ X23)
% 0.25/0.76          | ~ (l1_pre_topc @ X21)
% 0.25/0.76          | ~ (v2_pre_topc @ X21)
% 0.25/0.76          | (v2_struct_0 @ X21))),
% 0.25/0.76      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.25/0.76  thf('114', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.76         ((v2_struct_0 @ X0)
% 0.25/0.76          | ~ (v2_pre_topc @ X0)
% 0.25/0.76          | ~ (l1_pre_topc @ X0)
% 0.25/0.76          | (v2_struct_0 @ sk_D)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.76          | ~ (v1_funct_1 @ X1)
% 0.25/0.76          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (m1_subset_1 @ X1 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.25/0.76          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.25/0.76          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.25/0.76          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.25/0.76              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.25/0.76             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.25/0.76          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.25/0.76          | ~ (m1_pre_topc @ X2 @ X0)
% 0.25/0.76          | (v2_struct_0 @ X2)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_B)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('sup-', [status(thm)], ['112', '113'])).
% 0.25/0.76  thf('115', plain,
% 0.25/0.76      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('clc', [status(thm)], ['106', '107'])).
% 0.25/0.76  thf('116', plain,
% 0.25/0.76      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('clc', [status(thm)], ['42', '43'])).
% 0.25/0.76  thf('117', plain,
% 0.25/0.76      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.25/0.76         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.25/0.76      inference('sup+', [status(thm)], ['66', '82'])).
% 0.25/0.76  thf('118', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.25/0.76      inference('demod', [status(thm)], ['116', '117'])).
% 0.25/0.76  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('120', plain, ((v2_pre_topc @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('121', plain,
% 0.25/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.76         ((v2_struct_0 @ X0)
% 0.25/0.76          | ~ (v2_pre_topc @ X0)
% 0.25/0.76          | ~ (l1_pre_topc @ X0)
% 0.25/0.76          | (v2_struct_0 @ sk_D)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.25/0.76          | ~ (v1_funct_1 @ X1)
% 0.25/0.76          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (m1_subset_1 @ X1 @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.25/0.76          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.25/0.76          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.25/0.76               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.25/0.76          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.25/0.76              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.25/0.76             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.25/0.76          | ~ (m1_pre_topc @ X2 @ X0)
% 0.25/0.76          | (v2_struct_0 @ X2)
% 0.25/0.76          | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('demod', [status(thm)], ['114', '115', '118', '119', '120'])).
% 0.25/0.76  thf('122', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         ((v2_struct_0 @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ X0)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.25/0.76              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.25/0.76             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.76          | ~ (m1_subset_1 @ sk_E @ 
% 0.25/0.76               (k1_zfmisc_1 @ 
% 0.25/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.25/0.76          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.25/0.76          | ~ (v1_funct_1 @ sk_E)
% 0.25/0.76          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_D)
% 0.25/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.25/0.76          | ~ (v2_pre_topc @ sk_A)
% 0.25/0.76          | (v2_struct_0 @ sk_A))),
% 0.25/0.76      inference('sup-', [status(thm)], ['109', '121'])).
% 0.25/0.76  thf('123', plain,
% 0.25/0.76      ((m1_subset_1 @ sk_E @ 
% 0.25/0.76        (k1_zfmisc_1 @ 
% 0.25/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('124', plain,
% 0.25/0.76      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('125', plain, ((v1_funct_1 @ sk_E)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('126', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('129', plain,
% 0.25/0.76      (![X0 : $i]:
% 0.25/0.76         ((v2_struct_0 @ sk_B)
% 0.25/0.76          | (v2_struct_0 @ X0)
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.25/0.76          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.25/0.76              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.25/0.76             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.25/0.76          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.25/0.76          | (v2_struct_0 @ sk_D)
% 0.25/0.76          | (v2_struct_0 @ sk_A))),
% 0.25/0.76      inference('demod', [status(thm)],
% 0.25/0.76                ['122', '123', '124', '125', '126', '127', '128'])).
% 0.25/0.76  thf('130', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_A)
% 0.25/0.76        | (v2_struct_0 @ sk_D)
% 0.25/0.76        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.25/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.25/0.76            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.25/0.76           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.25/0.76        | (v2_struct_0 @ sk_C)
% 0.25/0.76        | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('sup-', [status(thm)], ['1', '129'])).
% 0.25/0.76  thf('131', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('132', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_A)
% 0.25/0.76        | (v2_struct_0 @ sk_D)
% 0.25/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.25/0.76            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.25/0.76           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.25/0.76        | (v2_struct_0 @ sk_C)
% 0.25/0.76        | (v2_struct_0 @ sk_B))),
% 0.25/0.76      inference('demod', [status(thm)], ['130', '131'])).
% 0.25/0.76  thf('133', plain,
% 0.25/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.25/0.76          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.25/0.76           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.25/0.76          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('134', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_B)
% 0.25/0.76        | (v2_struct_0 @ sk_C)
% 0.25/0.76        | (v2_struct_0 @ sk_D)
% 0.25/0.76        | (v2_struct_0 @ sk_A))),
% 0.25/0.76      inference('sup-', [status(thm)], ['132', '133'])).
% 0.25/0.76  thf('135', plain, (~ (v2_struct_0 @ sk_B)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('136', plain,
% 0.25/0.76      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.25/0.76      inference('sup-', [status(thm)], ['134', '135'])).
% 0.25/0.76  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('138', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.25/0.76      inference('clc', [status(thm)], ['136', '137'])).
% 0.25/0.76  thf('139', plain, (~ (v2_struct_0 @ sk_C)),
% 0.25/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.76  thf('140', plain, ((v2_struct_0 @ sk_D)),
% 0.25/0.76      inference('clc', [status(thm)], ['138', '139'])).
% 0.25/0.76  thf('141', plain, ($false), inference('demod', [status(thm)], ['0', '140'])).
% 0.25/0.76  
% 0.25/0.76  % SZS output end Refutation
% 0.25/0.76  
% 0.25/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
