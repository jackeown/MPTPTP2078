%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g68gfWz3pI

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:06 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 684 expanded)
%              Number of leaves         :   28 ( 212 expanded)
%              Depth                    :   22
%              Number of atoms          : 2371 (25102 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('4',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X15 @ X17 @ X16 @ X14 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
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
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
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
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
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
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r2_funct_2 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( ( k1_funct_1 @ X3 @ ( sk_E @ X0 @ X3 @ X1 ) )
       != ( k1_funct_1 @ X0 @ ( sk_E @ X0 @ X3 @ X1 ) ) )
      | ( r2_funct_2 @ X1 @ X2 @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ( r2_funct_2 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_funct_2 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('28',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X15 @ X17 @ X16 @ X14 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['25','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('49',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X15 @ X17 @ X16 @ X14 @ X18 ) @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ),
    inference(demod,[status(thm)],['46','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('70',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( ( k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) @ X13 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('91',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( ( k2_tmap_1 @ X7 @ X5 @ X8 @ X6 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X8 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['88','104'])).

thf('106',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['88','104'])).

thf('107',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) ),
    inference(demod,[status(thm)],['67','105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

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

thf('109',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) @ ( k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X23 ) @ ( k2_tmap_1 @ X22 @ X20 @ X25 @ X21 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( k2_tmap_1 @ X22 @ X20 @ X25 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('110',plain,(
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
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('112',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('113',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
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
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['88','104'])).

thf('117',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['88','104'])).

thf('118',plain,(
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
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','124','125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','126'])).

thf('128',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['0','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g68gfWz3pI
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.72  % Solved by: fo/fo7.sh
% 0.48/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.72  % done 442 iterations in 0.258s
% 0.48/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.72  % SZS output start Refutation
% 0.48/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.72  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.48/0.72  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.48/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.72  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.48/0.72  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.48/0.72  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.48/0.72  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.48/0.72  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.48/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.48/0.72  thf(t78_tmap_1, conjecture,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.48/0.72             ( l1_pre_topc @ B ) ) =>
% 0.48/0.72           ( ![C:$i]:
% 0.48/0.72             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.48/0.72               ( ![D:$i]:
% 0.48/0.72                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.48/0.72                   ( ![E:$i]:
% 0.48/0.72                     ( ( ( v1_funct_1 @ E ) & 
% 0.48/0.72                         ( v1_funct_2 @
% 0.48/0.72                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.72                         ( m1_subset_1 @
% 0.48/0.72                           E @ 
% 0.48/0.72                           ( k1_zfmisc_1 @
% 0.48/0.72                             ( k2_zfmisc_1 @
% 0.48/0.72                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.72                       ( ( m1_pre_topc @ C @ D ) =>
% 0.48/0.72                         ( r2_funct_2 @
% 0.48/0.72                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.48/0.72                           ( k3_tmap_1 @
% 0.48/0.72                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.48/0.72                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.72    (~( ![A:$i]:
% 0.48/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.72            ( l1_pre_topc @ A ) ) =>
% 0.48/0.72          ( ![B:$i]:
% 0.48/0.72            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.48/0.72                ( l1_pre_topc @ B ) ) =>
% 0.48/0.72              ( ![C:$i]:
% 0.48/0.72                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.48/0.72                  ( ![D:$i]:
% 0.48/0.72                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.48/0.72                      ( ![E:$i]:
% 0.48/0.72                        ( ( ( v1_funct_1 @ E ) & 
% 0.48/0.72                            ( v1_funct_2 @
% 0.48/0.72                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.72                            ( m1_subset_1 @
% 0.48/0.72                              E @ 
% 0.48/0.72                              ( k1_zfmisc_1 @
% 0.48/0.72                                ( k2_zfmisc_1 @
% 0.48/0.72                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.72                          ( ( m1_pre_topc @ C @ D ) =>
% 0.48/0.72                            ( r2_funct_2 @
% 0.48/0.72                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.48/0.72                              ( k3_tmap_1 @
% 0.48/0.72                                A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.48/0.72                              ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.48/0.72    inference('cnf.neg', [status(esa)], [t78_tmap_1])).
% 0.48/0.72  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(t2_tsep_1, axiom,
% 0.48/0.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.48/0.72  thf('3', plain,
% 0.48/0.72      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.48/0.72  thf('4', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_E_1 @ 
% 0.48/0.72        (k1_zfmisc_1 @ 
% 0.48/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(dt_k3_tmap_1, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.48/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.72         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.48/0.72         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.48/0.72         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.48/0.72         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.72         ( m1_subset_1 @
% 0.48/0.72           E @ 
% 0.48/0.72           ( k1_zfmisc_1 @
% 0.48/0.72             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.72       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.48/0.72         ( v1_funct_2 @
% 0.48/0.72           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.48/0.72           ( u1_struct_0 @ B ) ) & 
% 0.48/0.72         ( m1_subset_1 @
% 0.48/0.72           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.48/0.72           ( k1_zfmisc_1 @
% 0.48/0.72             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.48/0.72  thf('5', plain,
% 0.48/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.72         (~ (m1_pre_topc @ X14 @ X15)
% 0.48/0.72          | ~ (m1_pre_topc @ X16 @ X15)
% 0.48/0.72          | ~ (l1_pre_topc @ X17)
% 0.48/0.72          | ~ (v2_pre_topc @ X17)
% 0.48/0.72          | (v2_struct_0 @ X17)
% 0.48/0.72          | ~ (l1_pre_topc @ X15)
% 0.48/0.72          | ~ (v2_pre_topc @ X15)
% 0.48/0.72          | (v2_struct_0 @ X15)
% 0.48/0.72          | ~ (v1_funct_1 @ X18)
% 0.48/0.72          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))
% 0.48/0.72          | ~ (m1_subset_1 @ X18 @ 
% 0.48/0.72               (k1_zfmisc_1 @ 
% 0.48/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))))
% 0.48/0.72          | (m1_subset_1 @ (k3_tmap_1 @ X15 @ X17 @ X16 @ X14 @ X18) @ 
% 0.48/0.72             (k1_zfmisc_1 @ 
% 0.48/0.72              (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17)))))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.48/0.72  thf('6', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72           (k1_zfmisc_1 @ 
% 0.48/0.72            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.48/0.72          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.72               (u1_struct_0 @ sk_B))
% 0.48/0.72          | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72          | (v2_struct_0 @ X1)
% 0.48/0.72          | ~ (v2_pre_topc @ X1)
% 0.48/0.72          | ~ (l1_pre_topc @ X1)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_B)
% 0.48/0.72          | ~ (l1_pre_topc @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.72  thf('7', plain,
% 0.48/0.72      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('8', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('11', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72           (k1_zfmisc_1 @ 
% 0.48/0.72            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.48/0.72          | (v2_struct_0 @ X1)
% 0.48/0.72          | ~ (v2_pre_topc @ X1)
% 0.48/0.72          | ~ (l1_pre_topc @ X1)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.48/0.72  thf('12', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_A)
% 0.48/0.72          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72             (k1_zfmisc_1 @ 
% 0.48/0.72              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.48/0.72      inference('sup-', [status(thm)], ['3', '11'])).
% 0.48/0.72  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('16', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | (v2_struct_0 @ sk_A)
% 0.48/0.72          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72             (k1_zfmisc_1 @ 
% 0.48/0.72              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.48/0.72      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.48/0.72  thf('17', plain,
% 0.48/0.72      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72         (k1_zfmisc_1 @ 
% 0.48/0.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.48/0.72        | (v2_struct_0 @ sk_A)
% 0.48/0.72        | (v2_struct_0 @ sk_B))),
% 0.48/0.72      inference('sup-', [status(thm)], ['2', '16'])).
% 0.48/0.72  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('19', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_B)
% 0.48/0.72        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72           (k1_zfmisc_1 @ 
% 0.48/0.72            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.48/0.72      inference('clc', [status(thm)], ['17', '18'])).
% 0.48/0.72  thf('20', plain, (~ (v2_struct_0 @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('21', plain,
% 0.48/0.72      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72        (k1_zfmisc_1 @ 
% 0.48/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.72      inference('clc', [status(thm)], ['19', '20'])).
% 0.48/0.72  thf(d9_funct_2, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.48/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.72       ( ![D:$i]:
% 0.48/0.72         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.48/0.72             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.48/0.72           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 0.48/0.72             ( ![E:$i]:
% 0.48/0.72               ( ( m1_subset_1 @ E @ A ) =>
% 0.48/0.72                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 0.48/0.72  thf('22', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.72         (~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.48/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.48/0.72          | ((k1_funct_1 @ X3 @ (sk_E @ X0 @ X3 @ X1))
% 0.48/0.72              != (k1_funct_1 @ X0 @ (sk_E @ X0 @ X3 @ X1)))
% 0.48/0.72          | (r2_funct_2 @ X1 @ X2 @ X3 @ X0)
% 0.48/0.72          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.48/0.72          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.48/0.72          | ~ (v1_funct_1 @ X3))),
% 0.48/0.72      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.48/0.72  thf('23', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (v1_funct_1 @ X0)
% 0.48/0.72          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.48/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.48/0.72          | (r2_funct_2 @ X2 @ X1 @ X0 @ X0)
% 0.48/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.48/0.72          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.48/0.72          | ~ (v1_funct_1 @ X0))),
% 0.48/0.72      inference('eq_res', [status(thm)], ['22'])).
% 0.48/0.72  thf('24', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         ((r2_funct_2 @ X2 @ X1 @ X0 @ X0)
% 0.48/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.48/0.72          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.48/0.72          | ~ (v1_funct_1 @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['23'])).
% 0.48/0.72  thf('25', plain,
% 0.48/0.72      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))
% 0.48/0.72        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.48/0.72        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.72           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['21', '24'])).
% 0.48/0.72  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('27', plain,
% 0.48/0.72      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.48/0.72  thf('28', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_E_1 @ 
% 0.48/0.72        (k1_zfmisc_1 @ 
% 0.48/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('29', plain,
% 0.48/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.72         (~ (m1_pre_topc @ X14 @ X15)
% 0.48/0.72          | ~ (m1_pre_topc @ X16 @ X15)
% 0.48/0.72          | ~ (l1_pre_topc @ X17)
% 0.48/0.72          | ~ (v2_pre_topc @ X17)
% 0.48/0.72          | (v2_struct_0 @ X17)
% 0.48/0.72          | ~ (l1_pre_topc @ X15)
% 0.48/0.72          | ~ (v2_pre_topc @ X15)
% 0.48/0.72          | (v2_struct_0 @ X15)
% 0.48/0.72          | ~ (v1_funct_1 @ X18)
% 0.48/0.72          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))
% 0.48/0.72          | ~ (m1_subset_1 @ X18 @ 
% 0.48/0.72               (k1_zfmisc_1 @ 
% 0.48/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))))
% 0.48/0.72          | (v1_funct_1 @ (k3_tmap_1 @ X15 @ X17 @ X16 @ X14 @ X18)))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.48/0.72  thf('30', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1))
% 0.48/0.72          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.72               (u1_struct_0 @ sk_B))
% 0.48/0.72          | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72          | (v2_struct_0 @ X1)
% 0.48/0.72          | ~ (v2_pre_topc @ X1)
% 0.48/0.72          | ~ (l1_pre_topc @ X1)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_B)
% 0.48/0.72          | ~ (l1_pre_topc @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.72  thf('31', plain,
% 0.48/0.72      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('32', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('35', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1))
% 0.48/0.72          | (v2_struct_0 @ X1)
% 0.48/0.72          | ~ (v2_pre_topc @ X1)
% 0.48/0.72          | ~ (l1_pre_topc @ X1)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.48/0.72  thf('36', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_A)
% 0.48/0.72          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['27', '35'])).
% 0.48/0.72  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('40', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | (v2_struct_0 @ sk_A)
% 0.48/0.72          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1)))),
% 0.48/0.72      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.48/0.72  thf('41', plain,
% 0.48/0.72      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))
% 0.48/0.72        | (v2_struct_0 @ sk_A)
% 0.48/0.72        | (v2_struct_0 @ sk_B))),
% 0.48/0.72      inference('sup-', [status(thm)], ['26', '40'])).
% 0.48/0.72  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('43', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_B)
% 0.48/0.72        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)))),
% 0.48/0.72      inference('clc', [status(thm)], ['41', '42'])).
% 0.48/0.72  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('45', plain,
% 0.48/0.72      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))),
% 0.48/0.72      inference('clc', [status(thm)], ['43', '44'])).
% 0.48/0.72  thf('46', plain,
% 0.48/0.72      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.48/0.72        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.72           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)))),
% 0.48/0.72      inference('demod', [status(thm)], ['25', '45'])).
% 0.48/0.72  thf('47', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('48', plain,
% 0.48/0.72      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.48/0.72  thf('49', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_E_1 @ 
% 0.48/0.72        (k1_zfmisc_1 @ 
% 0.48/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('50', plain,
% 0.48/0.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.72         (~ (m1_pre_topc @ X14 @ X15)
% 0.48/0.72          | ~ (m1_pre_topc @ X16 @ X15)
% 0.48/0.72          | ~ (l1_pre_topc @ X17)
% 0.48/0.72          | ~ (v2_pre_topc @ X17)
% 0.48/0.72          | (v2_struct_0 @ X17)
% 0.48/0.72          | ~ (l1_pre_topc @ X15)
% 0.48/0.72          | ~ (v2_pre_topc @ X15)
% 0.48/0.72          | (v2_struct_0 @ X15)
% 0.48/0.72          | ~ (v1_funct_1 @ X18)
% 0.48/0.72          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))
% 0.48/0.72          | ~ (m1_subset_1 @ X18 @ 
% 0.48/0.72               (k1_zfmisc_1 @ 
% 0.48/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))))
% 0.48/0.72          | (v1_funct_2 @ (k3_tmap_1 @ X15 @ X17 @ X16 @ X14 @ X18) @ 
% 0.48/0.72             (u1_struct_0 @ X14) @ (u1_struct_0 @ X17)))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.48/0.72  thf('51', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.48/0.72          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.72               (u1_struct_0 @ sk_B))
% 0.48/0.72          | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72          | (v2_struct_0 @ X1)
% 0.48/0.72          | ~ (v2_pre_topc @ X1)
% 0.48/0.72          | ~ (l1_pre_topc @ X1)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_B)
% 0.48/0.72          | ~ (l1_pre_topc @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.48/0.72      inference('sup-', [status(thm)], ['49', '50'])).
% 0.48/0.72  thf('52', plain,
% 0.48/0.72      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('53', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('56', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.48/0.72          | (v2_struct_0 @ X1)
% 0.48/0.72          | ~ (v2_pre_topc @ X1)
% 0.48/0.72          | ~ (l1_pre_topc @ X1)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.48/0.72  thf('57', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_A)
% 0.48/0.72          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['48', '56'])).
% 0.48/0.72  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('61', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | (v2_struct_0 @ sk_A)
% 0.48/0.72          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1) @ 
% 0.48/0.72             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.48/0.72      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.48/0.72  thf('62', plain,
% 0.48/0.72      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.48/0.72        | (v2_struct_0 @ sk_A)
% 0.48/0.72        | (v2_struct_0 @ sk_B))),
% 0.48/0.72      inference('sup-', [status(thm)], ['47', '61'])).
% 0.48/0.72  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('64', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_B)
% 0.48/0.72        | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.48/0.72      inference('clc', [status(thm)], ['62', '63'])).
% 0.48/0.72  thf('65', plain, (~ (v2_struct_0 @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('66', plain,
% 0.48/0.72      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.48/0.72      inference('clc', [status(thm)], ['64', '65'])).
% 0.48/0.72  thf('67', plain,
% 0.48/0.72      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.72        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.48/0.72        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))),
% 0.48/0.72      inference('demod', [status(thm)], ['46', '66'])).
% 0.48/0.72  thf('68', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('69', plain,
% 0.48/0.72      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.48/0.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.48/0.72  thf('70', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_E_1 @ 
% 0.48/0.72        (k1_zfmisc_1 @ 
% 0.48/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(d5_tmap_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.48/0.72             ( l1_pre_topc @ B ) ) =>
% 0.48/0.72           ( ![C:$i]:
% 0.48/0.72             ( ( m1_pre_topc @ C @ A ) =>
% 0.48/0.72               ( ![D:$i]:
% 0.48/0.72                 ( ( m1_pre_topc @ D @ A ) =>
% 0.48/0.72                   ( ![E:$i]:
% 0.48/0.72                     ( ( ( v1_funct_1 @ E ) & 
% 0.48/0.72                         ( v1_funct_2 @
% 0.48/0.72                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.48/0.72                         ( m1_subset_1 @
% 0.48/0.72                           E @ 
% 0.48/0.72                           ( k1_zfmisc_1 @
% 0.48/0.72                             ( k2_zfmisc_1 @
% 0.48/0.72                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.48/0.72                       ( ( m1_pre_topc @ D @ C ) =>
% 0.48/0.72                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.48/0.72                           ( k2_partfun1 @
% 0.48/0.72                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.48/0.72                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.72  thf('71', plain,
% 0.48/0.72      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X9)
% 0.48/0.72          | ~ (v2_pre_topc @ X9)
% 0.48/0.72          | ~ (l1_pre_topc @ X9)
% 0.48/0.72          | ~ (m1_pre_topc @ X10 @ X11)
% 0.48/0.72          | ~ (m1_pre_topc @ X10 @ X12)
% 0.48/0.72          | ((k3_tmap_1 @ X11 @ X9 @ X12 @ X10 @ X13)
% 0.48/0.72              = (k2_partfun1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9) @ 
% 0.48/0.72                 X13 @ (u1_struct_0 @ X10)))
% 0.48/0.72          | ~ (m1_subset_1 @ X13 @ 
% 0.48/0.72               (k1_zfmisc_1 @ 
% 0.48/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))))
% 0.48/0.72          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X9))
% 0.48/0.72          | ~ (v1_funct_1 @ X13)
% 0.48/0.72          | ~ (m1_pre_topc @ X12 @ X11)
% 0.48/0.72          | ~ (l1_pre_topc @ X11)
% 0.48/0.72          | ~ (v2_pre_topc @ X11)
% 0.48/0.72          | (v2_struct_0 @ X11))),
% 0.48/0.72      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.48/0.72  thf('72', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.48/0.72          | ~ (v1_funct_1 @ sk_E_1)
% 0.48/0.72          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.72               (u1_struct_0 @ sk_B))
% 0.48/0.72          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E_1)
% 0.48/0.72              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.72                 sk_E_1 @ (u1_struct_0 @ X1)))
% 0.48/0.72          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.48/0.72          | ~ (m1_pre_topc @ X1 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ sk_B)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_B)
% 0.48/0.72          | (v2_struct_0 @ sk_B))),
% 0.48/0.72      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.72  thf('73', plain, ((v1_funct_1 @ sk_E_1)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('74', plain,
% 0.48/0.72      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('77', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.48/0.72          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E_1)
% 0.48/0.72              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.72                 sk_E_1 @ (u1_struct_0 @ X1)))
% 0.48/0.72          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.48/0.72          | ~ (m1_pre_topc @ X1 @ X0)
% 0.48/0.72          | (v2_struct_0 @ sk_B))),
% 0.48/0.72      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 0.48/0.72  thf('78', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1)
% 0.48/0.72              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.72                 sk_E_1 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72          | (v2_struct_0 @ sk_A))),
% 0.48/0.72      inference('sup-', [status(thm)], ['69', '77'])).
% 0.48/0.72  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('82', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ sk_B)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.48/0.72          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1)
% 0.48/0.72              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.48/0.72                 sk_E_1 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.55/0.72  thf('83', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_A)
% 0.55/0.72          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E_1)
% 0.55/0.72              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72                 sk_E_1 @ (u1_struct_0 @ X0)))
% 0.55/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.72          | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('simplify', [status(thm)], ['82'])).
% 0.55/0.72  thf('84', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_B)
% 0.55/0.72        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)
% 0.55/0.72            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72               sk_E_1 @ (u1_struct_0 @ sk_D)))
% 0.55/0.72        | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['68', '83'])).
% 0.55/0.72  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('86', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_A)
% 0.55/0.72        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)
% 0.55/0.72            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72               sk_E_1 @ (u1_struct_0 @ sk_D))))),
% 0.55/0.72      inference('clc', [status(thm)], ['84', '85'])).
% 0.55/0.72  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('88', plain,
% 0.55/0.72      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)
% 0.55/0.72         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72            sk_E_1 @ (u1_struct_0 @ sk_D)))),
% 0.55/0.72      inference('clc', [status(thm)], ['86', '87'])).
% 0.55/0.72  thf('89', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('90', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_E_1 @ 
% 0.55/0.72        (k1_zfmisc_1 @ 
% 0.55/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(d4_tmap_1, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.72       ( ![B:$i]:
% 0.55/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.72             ( l1_pre_topc @ B ) ) =>
% 0.55/0.72           ( ![C:$i]:
% 0.55/0.72             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.72                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.72                 ( m1_subset_1 @
% 0.55/0.72                   C @ 
% 0.55/0.72                   ( k1_zfmisc_1 @
% 0.55/0.72                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.72               ( ![D:$i]:
% 0.55/0.72                 ( ( m1_pre_topc @ D @ A ) =>
% 0.55/0.72                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.55/0.72                     ( k2_partfun1 @
% 0.55/0.72                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.55/0.72                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.72  thf('91', plain,
% 0.55/0.72      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.72         ((v2_struct_0 @ X5)
% 0.55/0.72          | ~ (v2_pre_topc @ X5)
% 0.55/0.72          | ~ (l1_pre_topc @ X5)
% 0.55/0.72          | ~ (m1_pre_topc @ X6 @ X7)
% 0.55/0.72          | ((k2_tmap_1 @ X7 @ X5 @ X8 @ X6)
% 0.55/0.72              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X8 @ 
% 0.55/0.72                 (u1_struct_0 @ X6)))
% 0.55/0.72          | ~ (m1_subset_1 @ X8 @ 
% 0.55/0.72               (k1_zfmisc_1 @ 
% 0.55/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.55/0.72          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.55/0.72          | ~ (v1_funct_1 @ X8)
% 0.55/0.72          | ~ (l1_pre_topc @ X7)
% 0.55/0.72          | ~ (v2_pre_topc @ X7)
% 0.55/0.72          | (v2_struct_0 @ X7))),
% 0.55/0.72      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.55/0.72  thf('92', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_A)
% 0.55/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.72          | ~ (v1_funct_1 @ sk_E_1)
% 0.55/0.72          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.72               (u1_struct_0 @ sk_B))
% 0.55/0.72          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0)
% 0.55/0.72              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72                 sk_E_1 @ (u1_struct_0 @ X0)))
% 0.55/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.72          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.72          | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['90', '91'])).
% 0.55/0.72  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('95', plain, ((v1_funct_1 @ sk_E_1)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('96', plain,
% 0.55/0.72      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('99', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_A)
% 0.55/0.72          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0)
% 0.55/0.72              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72                 sk_E_1 @ (u1_struct_0 @ X0)))
% 0.55/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.72          | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)],
% 0.55/0.72                ['92', '93', '94', '95', '96', '97', '98'])).
% 0.55/0.72  thf('100', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_B)
% 0.55/0.72        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)
% 0.55/0.72            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72               sk_E_1 @ (u1_struct_0 @ sk_D)))
% 0.55/0.72        | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['89', '99'])).
% 0.55/0.72  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('102', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_A)
% 0.55/0.72        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)
% 0.55/0.72            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72               sk_E_1 @ (u1_struct_0 @ sk_D))))),
% 0.55/0.72      inference('clc', [status(thm)], ['100', '101'])).
% 0.55/0.72  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('104', plain,
% 0.55/0.72      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)
% 0.55/0.72         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72            sk_E_1 @ (u1_struct_0 @ sk_D)))),
% 0.55/0.72      inference('clc', [status(thm)], ['102', '103'])).
% 0.55/0.72  thf('105', plain,
% 0.55/0.72      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)
% 0.55/0.72         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))),
% 0.55/0.72      inference('sup+', [status(thm)], ['88', '104'])).
% 0.55/0.72  thf('106', plain,
% 0.55/0.72      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)
% 0.55/0.72         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))),
% 0.55/0.72      inference('sup+', [status(thm)], ['88', '104'])).
% 0.55/0.72  thf('107', plain,
% 0.55/0.72      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72        (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D) @ 
% 0.55/0.72        (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D))),
% 0.55/0.72      inference('demod', [status(thm)], ['67', '105', '106'])).
% 0.55/0.72  thf('108', plain,
% 0.55/0.72      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.55/0.72        (k1_zfmisc_1 @ 
% 0.55/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.72      inference('clc', [status(thm)], ['19', '20'])).
% 0.55/0.72  thf(t77_tmap_1, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.72       ( ![B:$i]:
% 0.55/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.72             ( l1_pre_topc @ B ) ) =>
% 0.55/0.72           ( ![C:$i]:
% 0.55/0.72             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.55/0.72               ( ![D:$i]:
% 0.55/0.72                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.72                   ( ![E:$i]:
% 0.55/0.72                     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.72                         ( v1_funct_2 @
% 0.55/0.72                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.72                         ( m1_subset_1 @
% 0.55/0.72                           E @ 
% 0.55/0.72                           ( k1_zfmisc_1 @
% 0.55/0.72                             ( k2_zfmisc_1 @
% 0.55/0.72                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.72                       ( ![F:$i]:
% 0.55/0.72                         ( ( ( v1_funct_1 @ F ) & 
% 0.55/0.72                             ( v1_funct_2 @
% 0.55/0.72                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.72                             ( m1_subset_1 @
% 0.55/0.72                               F @ 
% 0.55/0.72                               ( k1_zfmisc_1 @
% 0.55/0.72                                 ( k2_zfmisc_1 @
% 0.55/0.72                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.72                           ( ( ( r2_funct_2 @
% 0.55/0.72                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.72                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.55/0.72                               ( m1_pre_topc @ D @ C ) ) =>
% 0.55/0.72                             ( r2_funct_2 @
% 0.55/0.72                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.72                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.55/0.72                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.72  thf('109', plain,
% 0.55/0.72      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.55/0.72         ((v2_struct_0 @ X20)
% 0.55/0.72          | ~ (v2_pre_topc @ X20)
% 0.55/0.72          | ~ (l1_pre_topc @ X20)
% 0.55/0.72          | (v2_struct_0 @ X21)
% 0.55/0.72          | ~ (m1_pre_topc @ X21 @ X22)
% 0.55/0.72          | ~ (v1_funct_1 @ X23)
% 0.55/0.72          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 0.55/0.72          | ~ (m1_subset_1 @ X23 @ 
% 0.55/0.72               (k1_zfmisc_1 @ 
% 0.55/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 0.55/0.72          | (r2_funct_2 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20) @ 
% 0.55/0.72             (k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X23) @ 
% 0.55/0.72             (k2_tmap_1 @ X22 @ X20 @ X25 @ X21))
% 0.55/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20) @ X23 @ 
% 0.55/0.72               (k2_tmap_1 @ X22 @ X20 @ X25 @ X24))
% 0.55/0.72          | ~ (m1_pre_topc @ X21 @ X24)
% 0.55/0.72          | ~ (m1_subset_1 @ X25 @ 
% 0.55/0.72               (k1_zfmisc_1 @ 
% 0.55/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.55/0.72          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.55/0.72          | ~ (v1_funct_1 @ X25)
% 0.55/0.72          | ~ (m1_pre_topc @ X24 @ X22)
% 0.55/0.72          | (v2_struct_0 @ X24)
% 0.55/0.72          | ~ (l1_pre_topc @ X22)
% 0.55/0.72          | ~ (v2_pre_topc @ X22)
% 0.55/0.72          | (v2_struct_0 @ X22))),
% 0.55/0.72      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.55/0.72  thf('110', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((v2_struct_0 @ X0)
% 0.55/0.72          | ~ (v2_pre_topc @ X0)
% 0.55/0.72          | ~ (l1_pre_topc @ X0)
% 0.55/0.72          | (v2_struct_0 @ sk_D)
% 0.55/0.72          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.55/0.72          | ~ (v1_funct_1 @ X1)
% 0.55/0.72          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.55/0.72          | ~ (m1_subset_1 @ X1 @ 
% 0.55/0.72               (k1_zfmisc_1 @ 
% 0.55/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.55/0.72          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.55/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.55/0.72               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.55/0.72          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.55/0.72              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)) @ 
% 0.55/0.72             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.55/0.72          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.55/0.72               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.55/0.72          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))
% 0.55/0.72          | ~ (m1_pre_topc @ X2 @ X0)
% 0.55/0.72          | (v2_struct_0 @ X2)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.72          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.72          | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['108', '109'])).
% 0.55/0.72  thf('111', plain,
% 0.55/0.72      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.55/0.72        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.55/0.72      inference('clc', [status(thm)], ['64', '65'])).
% 0.55/0.72  thf('112', plain,
% 0.55/0.72      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))),
% 0.55/0.72      inference('clc', [status(thm)], ['43', '44'])).
% 0.55/0.72  thf('113', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('114', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('115', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((v2_struct_0 @ X0)
% 0.55/0.72          | ~ (v2_pre_topc @ X0)
% 0.55/0.72          | ~ (l1_pre_topc @ X0)
% 0.55/0.72          | (v2_struct_0 @ sk_D)
% 0.55/0.72          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.55/0.72          | ~ (v1_funct_1 @ X1)
% 0.55/0.72          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.55/0.72          | ~ (m1_subset_1 @ X1 @ 
% 0.55/0.72               (k1_zfmisc_1 @ 
% 0.55/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.55/0.72          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.55/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1) @ 
% 0.55/0.72               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.55/0.72          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.55/0.72              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1)) @ 
% 0.55/0.72             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.55/0.72          | ~ (m1_pre_topc @ X2 @ X0)
% 0.55/0.72          | (v2_struct_0 @ X2)
% 0.55/0.72          | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.55/0.72  thf('116', plain,
% 0.55/0.72      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)
% 0.55/0.72         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))),
% 0.55/0.72      inference('sup+', [status(thm)], ['88', '104'])).
% 0.55/0.72  thf('117', plain,
% 0.55/0.72      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)
% 0.55/0.72         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E_1))),
% 0.55/0.72      inference('sup+', [status(thm)], ['88', '104'])).
% 0.55/0.72  thf('118', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((v2_struct_0 @ X0)
% 0.55/0.72          | ~ (v2_pre_topc @ X0)
% 0.55/0.72          | ~ (l1_pre_topc @ X0)
% 0.55/0.72          | (v2_struct_0 @ sk_D)
% 0.55/0.72          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.55/0.72          | ~ (v1_funct_1 @ X1)
% 0.55/0.72          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.55/0.72          | ~ (m1_subset_1 @ X1 @ 
% 0.55/0.72               (k1_zfmisc_1 @ 
% 0.55/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.55/0.72          | ~ (m1_pre_topc @ X2 @ sk_D)
% 0.55/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72               (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D) @ 
% 0.55/0.72               (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_D))
% 0.55/0.72          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72             (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X2 @ 
% 0.55/0.72              (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)) @ 
% 0.55/0.72             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.55/0.72          | ~ (m1_pre_topc @ X2 @ X0)
% 0.55/0.72          | (v2_struct_0 @ X2)
% 0.55/0.72          | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.55/0.72  thf('119', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_B)
% 0.55/0.72          | (v2_struct_0 @ X0)
% 0.55/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.72          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.55/0.72              (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)) @ 
% 0.55/0.72             (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0))
% 0.55/0.72          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.55/0.72          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.55/0.72               (k1_zfmisc_1 @ 
% 0.55/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.72          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.72               (u1_struct_0 @ sk_B))
% 0.55/0.72          | ~ (v1_funct_1 @ sk_E_1)
% 0.55/0.72          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.55/0.72          | (v2_struct_0 @ sk_D)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.72          | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['107', '118'])).
% 0.55/0.72  thf('120', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_E_1 @ 
% 0.55/0.72        (k1_zfmisc_1 @ 
% 0.55/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('121', plain,
% 0.55/0.72      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('122', plain, ((v1_funct_1 @ sk_E_1)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('123', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('126', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_B)
% 0.55/0.72          | (v2_struct_0 @ X0)
% 0.55/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.55/0.72          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.55/0.72              (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)) @ 
% 0.55/0.72             (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ X0))
% 0.55/0.72          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.55/0.72          | (v2_struct_0 @ sk_D)
% 0.55/0.72          | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('demod', [status(thm)],
% 0.55/0.72                ['119', '120', '121', '122', '123', '124', '125'])).
% 0.55/0.72  thf('127', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_A)
% 0.55/0.72        | (v2_struct_0 @ sk_D)
% 0.55/0.72        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.55/0.72        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.55/0.72            (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)) @ 
% 0.55/0.72           (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_C))
% 0.55/0.72        | (v2_struct_0 @ sk_C)
% 0.55/0.72        | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('sup-', [status(thm)], ['1', '126'])).
% 0.55/0.72  thf('128', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('129', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_A)
% 0.55/0.72        | (v2_struct_0 @ sk_D)
% 0.55/0.72        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.55/0.72            (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)) @ 
% 0.55/0.72           (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_C))
% 0.55/0.72        | (v2_struct_0 @ sk_C)
% 0.55/0.72        | (v2_struct_0 @ sk_B))),
% 0.55/0.72      inference('demod', [status(thm)], ['127', '128'])).
% 0.55/0.72  thf('130', plain,
% 0.55/0.72      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.72          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.55/0.72           (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_D)) @ 
% 0.55/0.72          (k2_tmap_1 @ sk_A @ sk_B @ sk_E_1 @ sk_C))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('131', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_B)
% 0.55/0.72        | (v2_struct_0 @ sk_C)
% 0.55/0.72        | (v2_struct_0 @ sk_D)
% 0.55/0.72        | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['129', '130'])).
% 0.55/0.72  thf('132', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('133', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.55/0.72      inference('sup-', [status(thm)], ['131', '132'])).
% 0.55/0.72  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('135', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.55/0.72      inference('clc', [status(thm)], ['133', '134'])).
% 0.55/0.72  thf('136', plain, (~ (v2_struct_0 @ sk_C)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('137', plain, ((v2_struct_0 @ sk_D)),
% 0.55/0.72      inference('clc', [status(thm)], ['135', '136'])).
% 0.55/0.72  thf('138', plain, ($false), inference('demod', [status(thm)], ['0', '137'])).
% 0.55/0.72  
% 0.55/0.72  % SZS output end Refutation
% 0.55/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
