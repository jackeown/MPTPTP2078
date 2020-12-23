%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1811+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3yU7sENrm1

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:19 EST 2020

% Result     : Theorem 14.21s
% Output     : Refutation 14.31s
% Verified   : 
% Statistics : Number of formulae       :  287 (1096 expanded)
%              Number of leaves         :   26 ( 307 expanded)
%              Depth                    :   26
%              Number of atoms          : 5606 (106636 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   30 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t127_tmap_1,conjecture,(
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
                & ( v1_borsuk_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_borsuk_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                      <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                          & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v1_borsuk_1 @ C @ A )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_borsuk_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_tmap_1])).

thf('0',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_E )
   <= ~ ( v1_funct_1 @ sk_E ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    v1_funct_1 @ sk_E ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('8',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X12 @ X14 @ X13 @ X11 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X12 @ X14 @ X13 @ X11 @ X15 ) @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_D )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X12 @ X14 @ X13 @ X11 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A_1 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['3'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
   <= ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('134',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['135'])).

thf('137',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t126_tmap_1,axiom,(
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
                 => ( ( r4_tsep_1 @ A @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('138',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ X27 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X28 @ X27 ) @ X28 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( r4_tsep_1 @ X26 @ X28 @ X25 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('139',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( r4_tsep_1 @ X26 @ X28 @ X25 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X28 @ X27 ) @ X28 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v5_pre_topc @ X27 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X24 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ~ ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v2_pre_topc @ sk_A_1 )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['137','139'])).

thf('141',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ~ ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['140','141','142','143','144','145','146','147','148'])).

thf('150',plain,(
    v1_borsuk_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_borsuk_1 @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_borsuk_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_borsuk_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( r4_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('152',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_borsuk_1 @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( r4_tsep_1 @ X33 @ X32 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X33 )
      | ~ ( v1_borsuk_1 @ X34 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t87_tsep_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( r4_tsep_1 @ sk_A_1 @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_A_1 )
      | ( r4_tsep_1 @ sk_A_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,
    ( ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A_1 )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['150','157'])).

thf('159',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['149','162'])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['136','163'])).

thf('165',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['135'])).

thf('176',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ X27 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X25 @ X27 ) @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( r4_tsep_1 @ X26 @ X28 @ X25 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('178',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( r4_tsep_1 @ X26 @ X28 @ X25 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X25 @ X27 ) @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v5_pre_topc @ X27 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X24 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ~ ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_A_1 )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v2_pre_topc @ sk_A_1 )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['176','178'])).

thf('180',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ~ ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['179','180','181','182','183','184','185','186','187'])).

thf('189',plain,(
    r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['160','161'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['175','190'])).

thf('192',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('193',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('203',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['203'])).

thf('205',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
   <= ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 ) ),
    inference(split,[status(esa)],['205'])).

thf('207',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
   <= ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 ) ),
    inference(split,[status(esa)],['207'])).

thf('209',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(split,[status(esa)],['209'])).

thf('211',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(split,[status(esa)],['211'])).

thf('213',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X28 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X28 @ X27 ) @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X28 @ X27 ) @ X28 @ X24 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X25 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X25 @ X27 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X25 @ X27 ) @ X25 @ X24 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X26 @ X24 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X25 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ( v5_pre_topc @ X27 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ ( k1_tsep_1 @ X26 @ X28 @ X25 ) ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( r4_tsep_1 @ X26 @ X28 @ X25 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('214',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ~ ( v2_pre_topc @ sk_A_1 )
      | ~ ( l1_pre_topc @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A_1 )
      | ~ ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A_1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    m1_pre_topc @ sk_C @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    m1_pre_topc @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['214','215','216','217','218','219','220','221','222','223'])).

thf('225',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ~ ( r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['210','224'])).

thf('226',plain,(
    r4_tsep_1 @ sk_A_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['160','161'])).

thf('227',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['228'])).

thf('230',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['40'])).

thf('231',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) )
   <= ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['232'])).

thf('234',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['66'])).

thf('235',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) )
   <= ( v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['236'])).

thf('238',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['118'])).

thf('239',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_funct_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) )
   <= ( v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['240'])).

thf('242',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['131'])).

thf('243',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['241','242'])).

thf('244',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference(demod,[status(thm)],['227','231','235','239','243'])).

thf('245',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['92'])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['208','246'])).

thf('248',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A_1 ) )
   <= ( ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['206','247'])).

thf('249',plain,
    ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
   <= ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('250',plain,
    ( ( ( v2_struct_0 @ sk_A_1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
      & ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 )
      & ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_C @ sk_E ) @ sk_C @ sk_B_2 )
    | ( v5_pre_topc @ sk_E @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_B_2 )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A_1 @ sk_B_2 @ ( k1_tsep_1 @ sk_A_1 @ sk_C @ sk_D ) @ sk_D @ sk_E ) @ sk_D @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','5','8','40','66','92','105','118','131','134','174','201','202','204','258'])).


%------------------------------------------------------------------------------
