%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1781+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CGnFjyXu0c

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 469 expanded)
%              Number of leaves         :   36 ( 157 expanded)
%              Depth                    :   32
%              Number of atoms          : 2616 (12265 expanded)
%              Number of equality atoms :   41 ( 219 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_struct_0_type,type,(
    k3_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(t96_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                     => ( D
                        = ( k1_funct_1 @ C @ D ) ) ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                       => ( D
                          = ( k1_funct_1 @ C @ D ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( v1_funct_1 @ ( k3_struct_0 @ A ) )
        & ( v1_funct_2 @ ( k3_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k3_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k3_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( v1_funct_2 @ ( k3_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( k3_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf(d4_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k3_struct_0 @ A )
        = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k3_struct_0 @ X0 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_struct_0])).

thf('5',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k3_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( v1_funct_2 @ ( k3_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( k3_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf(t59_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X18 @ X16 @ X19 @ X15 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tmap_1 @ X15 @ X17 @ X16 @ X19 ) @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X15 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k2_tmap_1 @ X0 @ X0 @ ( k3_struct_0 @ X0 ) @ X1 ) @ X2 )
      | ( m1_subset_1 @ ( sk_F @ X2 @ ( k3_struct_0 @ X0 ) @ X1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k3_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( sk_F @ X2 @ ( k3_struct_0 @ X0 ) @ X1 @ X0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k2_tmap_1 @ X0 @ X0 @ ( k3_struct_0 @ X0 ) @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( k4_tmap_1 @ A @ B )
            = ( k2_tmap_1 @ A @ A @ ( k3_struct_0 @ A ) @ B ) ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( k4_tmap_1 @ X2 @ X1 )
        = ( k2_tmap_1 @ X2 @ X2 @ ( k3_struct_0 @ X2 ) @ X1 ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d7_tmap_1])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k4_tmap_1 @ sk_A @ sk_B )
      = ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_tmap_1 @ sk_A @ sk_B )
      = ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','15','16','17','18','19','20','28'])).

thf('30',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('37',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X14 ) @ X13 )
        = X13 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k6_partfun1 @ X10 )
      = ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( k6_partfun1 @ X14 ) @ X13 )
        = X13 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
      = ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
      = ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('44',plain,
    ( ( ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
      = ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k3_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('47',plain,(
    ! [X3: $i] :
      ( ( v1_funct_2 @ ( k3_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('48',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( k3_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ X7 )
      | ( ( k3_funct_2 @ X7 @ X8 @ X6 @ X9 )
        = ( k1_funct_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_struct_0 @ X0 ) @ X1 )
        = ( k1_funct_1 @ ( k3_struct_0 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_struct_0 @ X0 ) @ X1 )
        = ( k1_funct_1 @ ( k3_struct_0 @ X0 ) @ X1 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k3_struct_0 @ X0 ) @ X1 )
        = ( k1_funct_1 @ ( k3_struct_0 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
      = ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('55',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
      = ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
      = ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['45','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('58',plain,
    ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
      = ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ X16 @ ( sk_F @ X18 @ X16 @ X19 @ X15 @ X17 ) )
       != ( k1_funct_1 @ X18 @ ( sk_F @ X18 @ X16 @ X19 @ X15 @ X17 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tmap_1 @ X15 @ X17 @ X16 @ X19 ) @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X15 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('60',plain,
    ( ( ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
     != ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k3_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('62',plain,(
    ! [X3: $i] :
      ( ( v1_funct_1 @ ( k3_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('63',plain,(
    ! [X3: $i] :
      ( ( v1_funct_2 @ ( k3_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( k3_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_struct_0])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X18 @ X16 @ X19 @ X15 @ X17 ) @ ( u1_struct_0 @ X19 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tmap_1 @ X15 @ X17 @ X16 @ X19 ) @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X15 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k2_tmap_1 @ X0 @ X0 @ ( k3_struct_0 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_F @ X2 @ ( k3_struct_0 @ X0 ) @ X1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ ( k3_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ ( k3_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ ( k3_struct_0 @ X0 ) @ X1 @ X0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k2_tmap_1 @ X0 @ X0 @ ( k3_struct_0 @ X0 ) @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75','76'])).

thf('78',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ ( u1_struct_0 @ sk_B ) )
      | ( X20
        = ( k1_funct_1 @ sk_C @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['61','85'])).

thf('87',plain,
    ( ( ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A )
    = ( k1_funct_1 @ sk_C @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k4_tmap_1 @ sk_A @ sk_B )
    = ( k2_tmap_1 @ sk_A @ sk_A @ ( k3_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
     != ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k3_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','93','94','95','96','97','98','99','100','101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k1_funct_1 @ ( k3_struct_0 @ sk_A ) @ ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
     != ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A )
     != ( sk_F @ sk_C @ ( k3_struct_0 @ sk_A ) @ sk_B @ sk_A @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','104'])).

thf('106',plain,
    ( ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k3_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( v1_funct_2 @ ( k3_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ ( k3_struct_0 @ sk_A ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['1','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['119','120'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('122',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('125',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['0','125'])).


%------------------------------------------------------------------------------
