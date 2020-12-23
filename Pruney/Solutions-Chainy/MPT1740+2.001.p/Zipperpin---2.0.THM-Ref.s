%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uLb7RZlFHo

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 862 expanded)
%              Number of leaves         :   27 ( 259 expanded)
%              Depth                    :   30
%              Number of atoms          : 2883 (25057 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   26 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t49_tmap_1,conjecture,(
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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ( v5_pre_topc @ C @ B @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    | ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
   <= ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tmap_1,axiom,(
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
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r1_tmap_1 @ A @ B @ C @ D )
                  <=> ! [E: $i] :
                        ( ( m1_connsp_2 @ E @ B @ ( k3_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) )
                       => ? [F: $i] :
                            ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ F ) @ E )
                            & ( m1_connsp_2 @ F @ A @ D ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( m1_connsp_2 @ ( sk_E @ X1 @ X3 @ X0 @ X2 ) @ X0 @ ( k3_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) )
      | ( r1_tmap_1 @ X2 @ X0 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_tmap_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
      | ( m1_connsp_2 @ ( sk_E @ X0 @ sk_C @ sk_A @ sk_B ) @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
      | ( m1_connsp_2 @ ( sk_E @ X0 @ sk_C @ sk_A @ sk_B ) @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12','13','14'])).

thf('16',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    ! [X12: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12 )
      | ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
   <= ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_borsuk_1,axiom,(
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
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_connsp_2 @ E @ B @ ( k3_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) )
                       => ? [F: $i] :
                            ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ F ) @ E )
                            & ( m1_connsp_2 @ F @ A @ D ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_connsp_2 @ X9 @ X6 @ ( k3_funct_2 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ X10 ) )
      | ( m1_connsp_2 @ ( sk_F_1 @ X9 @ X10 @ X7 @ X6 @ X8 ) @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_borsuk_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) @ sk_B @ X0 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26','27'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
        | ( m1_connsp_2 @ ( sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ( m1_connsp_2 @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_connsp_2 @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( m1_connsp_2 @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf('35',plain,
    ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
   <= ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_connsp_2 @ X9 @ X6 @ ( k3_funct_2 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ X10 ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ ( sk_F_1 @ X9 @ X10 @ X7 @ X6 @ X8 ) ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_borsuk_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) ) @ X1 )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42','43','44'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
        | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) ) @ X1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_connsp_2 @ X4 @ X2 @ X1 )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X4 ) @ ( sk_E @ X1 @ X3 @ X0 @ X2 ) )
      | ( r1_tmap_1 @ X2 @ X0 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_tmap_1])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_B @ sk_D_1 )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ~ ( m1_connsp_2 @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','57','58','59','60'])).

thf('62',plain,
    ( ( ~ ( m1_connsp_2 @ ( sk_F_1 @ ( sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_D_1 @ sk_C @ sk_A @ sk_B ) @ sk_B @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','62'])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
   <= ( ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','70'])).

thf('72',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_borsuk_1])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80','81'])).

thf('84',plain,
    ( ! [X12: $i] :
        ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12 ) )
   <= ! [X12: $i] :
        ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) )
   <= ! [X12: $i] :
        ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X12: $i] :
        ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12 ) )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('87',plain,(
    ! [X12: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','70','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X7 @ X6 @ X8 ) @ X6 @ ( k3_funct_2 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ ( sk_D @ X7 @ X6 @ X8 ) ) )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_borsuk_1])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ X3 @ X1 )
      | ( m1_connsp_2 @ ( sk_F @ X5 @ X1 @ X3 @ X0 @ X2 ) @ X2 @ X1 )
      | ~ ( m1_connsp_2 @ X5 @ X0 @ ( k3_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_tmap_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ( m1_connsp_2 @ ( sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) @ sk_B @ X0 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ( m1_connsp_2 @ ( sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) @ sk_B @ X0 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['98','108'])).

thf('110',plain,
    ( ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','110'])).

thf('112',plain,
    ( ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','112'])).

thf('114',plain,
    ( ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80','81'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','87'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( m1_connsp_2 @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94','95','96','97'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( r1_tmap_1 @ X2 @ X0 @ X3 @ X1 )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( sk_F @ X5 @ X1 @ X3 @ X0 @ X2 ) ) @ X5 )
      | ~ ( m1_connsp_2 @ X5 @ X0 @ ( k3_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_tmap_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_connsp_2 @ X1 @ sk_A @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B ) ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','127'])).

thf('129',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','129'])).

thf('131',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','131'])).

thf('133',plain,
    ( ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) ) @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X6: $i,X7: $i,X8: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_connsp_2 @ X11 @ X8 @ ( sk_D @ X7 @ X6 @ X8 ) )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ X11 ) @ ( sk_E_1 @ X7 @ X6 @ X8 ) )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_borsuk_1])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ~ ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ~ ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140','141','142'])).

thf('144',plain,
    ( ~ ( m1_connsp_2 @ ( sk_F @ ( sk_E_1 @ sk_C @ sk_A @ sk_B ) @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ sk_C @ sk_A @ sk_B ) @ sk_B @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v5_pre_topc @ sk_C @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['72','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uLb7RZlFHo
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 61 iterations in 0.041s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.51  thf(t49_tmap_1, conjecture,
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
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51                ( l1_pre_topc @ B ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                    ( v1_funct_2 @
% 0.21/0.51                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.51                    ( m1_subset_1 @
% 0.21/0.51                      C @ 
% 0.21/0.51                      ( k1_zfmisc_1 @
% 0.21/0.51                        ( k2_zfmisc_1 @
% 0.21/0.51                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.51                  ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.21/0.51                    ( ![D:$i]:
% 0.21/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.51                        ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t49_tmap_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51        | ~ (v5_pre_topc @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((~ (v5_pre_topc @ sk_C @ sk_B @ sk_A))
% 0.21/0.51         <= (~ ((v5_pre_topc @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (~ ((v5_pre_topc @ sk_C @ sk_B @ sk_A)) | 
% 0.21/0.51       ~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (v5_pre_topc @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))) | 
% 0.21/0.51       ~ ((v5_pre_topc @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                   ( ( r1_tmap_1 @ A @ B @ C @ D ) <=>
% 0.21/0.51                     ( ![E:$i]:
% 0.21/0.51                       ( ( m1_connsp_2 @
% 0.21/0.51                           E @ B @ 
% 0.21/0.51                           ( k3_funct_2 @
% 0.21/0.51                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) =>
% 0.21/0.51                         ( ?[F:$i]:
% 0.21/0.51                           ( ( r1_tarski @
% 0.21/0.51                               ( k7_relset_1 @
% 0.21/0.51                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.51                                 C @ F ) @ 
% 0.21/0.51                               E ) & 
% 0.21/0.51                             ( m1_connsp_2 @ F @ A @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | (m1_connsp_2 @ (sk_E @ X1 @ X3 @ X0 @ X2) @ X0 @ 
% 0.21/0.51             (k3_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ X1))
% 0.21/0.51          | (r1_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.21/0.51          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (v1_funct_1 @ X3)
% 0.21/0.51          | ~ (l1_pre_topc @ X2)
% 0.21/0.51          | ~ (v2_pre_topc @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tmap_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 0.21/0.51          | (m1_connsp_2 @ (sk_E @ X0 @ sk_C @ sk_A @ sk_B) @ sk_A @ 
% 0.21/0.51             (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              sk_C @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 0.21/0.51          | (m1_connsp_2 @ (sk_E @ X0 @ sk_C @ sk_A @ sk_B) @ sk_A @ 
% 0.21/0.51             (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              sk_C @ X0))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['8', '9', '10', '11', '12', '13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A)
% 0.21/0.51         | (m1_connsp_2 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_A @ 
% 0.21/0.51            (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51             sk_D_1))
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X12 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12)
% 0.21/0.51          | (v5_pre_topc @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((v5_pre_topc @ sk_C @ sk_B @ sk_A))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_borsuk_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.21/0.51                 ( ![D:$i]:
% 0.21/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51                     ( ![E:$i]:
% 0.21/0.51                       ( ( m1_connsp_2 @
% 0.21/0.51                           E @ B @ 
% 0.21/0.51                           ( k3_funct_2 @
% 0.21/0.51                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) ) =>
% 0.21/0.51                         ( ?[F:$i]:
% 0.21/0.51                           ( ( r1_tarski @
% 0.21/0.51                               ( k7_relset_1 @
% 0.21/0.51                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.51                                 C @ F ) @ 
% 0.21/0.51                               E ) & 
% 0.21/0.51                             ( m1_connsp_2 @ F @ A @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X6)
% 0.21/0.51          | ~ (v2_pre_topc @ X6)
% 0.21/0.51          | ~ (l1_pre_topc @ X6)
% 0.21/0.51          | ~ (v5_pre_topc @ X7 @ X8 @ X6)
% 0.21/0.51          | ~ (m1_connsp_2 @ X9 @ X6 @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7 @ X10))
% 0.21/0.51          | (m1_connsp_2 @ (sk_F_1 @ X9 @ X10 @ X7 @ X6 @ X8) @ X8 @ X10)
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.21/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (l1_pre_topc @ X8)
% 0.21/0.51          | ~ (v2_pre_topc @ X8)
% 0.21/0.51          | (v2_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_borsuk_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (m1_connsp_2 @ (sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B) @ sk_B @ X0)
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | ~ (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (m1_connsp_2 @ (sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B) @ sk_B @ X0)
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | ~ (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['21', '22', '23', '24', '25', '26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((![X0 : $i, X1 : $i]:
% 0.21/0.51          ((v2_struct_0 @ sk_A)
% 0.21/0.51           | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51                (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                 sk_C @ X0))
% 0.21/0.51           | (m1_connsp_2 @ (sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B) @ sk_B @ X0)
% 0.21/0.51           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51           | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | ~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51         | (m1_connsp_2 @ 
% 0.21/0.51            (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51             sk_A @ sk_B) @ 
% 0.21/0.51            sk_B @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | (m1_connsp_2 @ 
% 0.21/0.51            (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51             sk_A @ sk_B) @ 
% 0.21/0.51            sk_B @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((((m1_connsp_2 @ 
% 0.21/0.51          (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51           sk_A @ sk_B) @ 
% 0.21/0.51          sk_B @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A)
% 0.21/0.51         | (m1_connsp_2 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_A @ 
% 0.21/0.51            (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51             sk_D_1))
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '15'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((v5_pre_topc @ sk_C @ sk_B @ sk_A))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['17'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X6)
% 0.21/0.51          | ~ (v2_pre_topc @ X6)
% 0.21/0.51          | ~ (l1_pre_topc @ X6)
% 0.21/0.51          | ~ (v5_pre_topc @ X7 @ X8 @ X6)
% 0.21/0.51          | ~ (m1_connsp_2 @ X9 @ X6 @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7 @ X10))
% 0.21/0.51          | (r1_tarski @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7 @ 
% 0.21/0.51              (sk_F_1 @ X9 @ X10 @ X7 @ X6 @ X8)) @ 
% 0.21/0.51             X9)
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.21/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (l1_pre_topc @ X8)
% 0.21/0.51          | ~ (v2_pre_topc @ X8)
% 0.21/0.51          | (v2_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_borsuk_1])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (r1_tarski @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              sk_C @ (sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | ~ (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (r1_tarski @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              sk_C @ (sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | ~ (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['38', '39', '40', '41', '42', '43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((![X0 : $i, X1 : $i]:
% 0.21/0.51          ((v2_struct_0 @ sk_A)
% 0.21/0.51           | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51                (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                 sk_C @ X0))
% 0.21/0.51           | (r1_tarski @ 
% 0.21/0.51              (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51               sk_C @ (sk_F_1 @ X1 @ X0 @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51              X1)
% 0.21/0.51           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51           | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | ~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51         | (r1_tarski @ 
% 0.21/0.51            (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51             sk_C @ 
% 0.21/0.51             (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51              sk_A @ sk_B)) @ 
% 0.21/0.51            (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B))
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tarski @ 
% 0.21/0.51            (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51             sk_C @ 
% 0.21/0.51             (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51              sk_A @ sk_B)) @ 
% 0.21/0.51            (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B))
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      ((((r1_tarski @ 
% 0.21/0.51          (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51           (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51            sk_A @ sk_B)) @ 
% 0.21/0.51          (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B))
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (m1_connsp_2 @ X4 @ X2 @ X1)
% 0.21/0.51          | ~ (r1_tarski @ 
% 0.21/0.51               (k7_relset_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ X4) @ 
% 0.21/0.51               (sk_E @ X1 @ X3 @ X0 @ X2))
% 0.21/0.51          | (r1_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.21/0.51          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (v1_funct_1 @ X3)
% 0.21/0.51          | ~ (l1_pre_topc @ X2)
% 0.21/0.51          | ~ (v2_pre_topc @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tmap_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51         | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51         | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51         | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.51              (k1_zfmisc_1 @ 
% 0.21/0.51               (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | ~ (m1_connsp_2 @ 
% 0.21/0.51              (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51               sk_A @ sk_B) @ 
% 0.21/0.51              sk_B @ sk_D_1)
% 0.21/0.51         | ~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.21/0.51         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51         | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['3'])).
% 0.21/0.51  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | ~ (m1_connsp_2 @ 
% 0.21/0.51              (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51               sk_A @ sk_B) @ 
% 0.21/0.51              sk_B @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['52', '53', '54', '55', '56', '57', '58', '59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (((~ (m1_connsp_2 @ 
% 0.21/0.51            (sk_F_1 @ (sk_E @ sk_D_1 @ sk_C @ sk_A @ sk_B) @ sk_D_1 @ sk_C @ 
% 0.21/0.51             sk_A @ sk_B) @ 
% 0.21/0.51            sk_B @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_A)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 0.21/0.51         | (v2_struct_0 @ sk_B)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.51  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_B) | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1))
% 0.21/0.51         <= (((v5_pre_topc @ sk_C @ sk_B @ sk_A)) & 
% 0.21/0.51             ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1))
% 0.21/0.51         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (~ ((v5_pre_topc @ sk_C @ sk_B @ sk_A)) | 
% 0.21/0.51       ~ ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))) | 
% 0.21/0.51       ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain, (~ ((v5_pre_topc @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['2', '4', '70'])).
% 0.21/0.51  thf('72', plain, (~ (v5_pre_topc @ sk_C @ sk_B @ sk_A)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['1', '71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X6)
% 0.21/0.51          | ~ (v2_pre_topc @ X6)
% 0.21/0.51          | ~ (l1_pre_topc @ X6)
% 0.21/0.51          | (m1_subset_1 @ (sk_D @ X7 @ X6 @ X8) @ (u1_struct_0 @ X8))
% 0.21/0.51          | (v5_pre_topc @ X7 @ X8 @ X6)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.21/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (l1_pre_topc @ X8)
% 0.21/0.51          | ~ (v2_pre_topc @ X8)
% 0.21/0.51          | (v2_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_borsuk_1])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['75', '76', '77', '78', '79', '80', '81'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['75', '76', '77', '78', '79', '80', '81'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      ((![X12 : $i]:
% 0.21/0.51          (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_B))
% 0.21/0.51           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12)))
% 0.21/0.51         <= ((![X12 : $i]:
% 0.21/0.51                (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_B))
% 0.21/0.51                 | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12))))),
% 0.21/0.51      inference('split', [status(esa)], ['17'])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      ((((v2_struct_0 @ sk_A)
% 0.21/0.51         | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))))
% 0.21/0.51         <= ((![X12 : $i]:
% 0.21/0.51                (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_B))
% 0.21/0.51                 | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      ((![X12 : $i]:
% 0.21/0.51          (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_B))
% 0.21/0.51           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12))) | 
% 0.21/0.51       ((v5_pre_topc @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('split', [status(esa)], ['17'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      ((![X12 : $i]:
% 0.21/0.51          (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ sk_B))
% 0.21/0.51           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X12)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['2', '4', '70', '86'])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X6)
% 0.21/0.51          | ~ (v2_pre_topc @ X6)
% 0.21/0.51          | ~ (l1_pre_topc @ X6)
% 0.21/0.51          | (m1_connsp_2 @ (sk_E_1 @ X7 @ X6 @ X8) @ X6 @ 
% 0.21/0.51             (k3_funct_2 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7 @ 
% 0.21/0.51              (sk_D @ X7 @ X6 @ X8)))
% 0.21/0.51          | (v5_pre_topc @ X7 @ X8 @ X6)
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.21/0.51          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (l1_pre_topc @ X8)
% 0.21/0.51          | ~ (v2_pre_topc @ X8)
% 0.21/0.51          | (v2_struct_0 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_borsuk_1])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (m1_connsp_2 @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ sk_A @ 
% 0.21/0.51           (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51            (sk_D @ sk_C @ sk_A @ sk_B)))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.51  thf('92', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (m1_connsp_2 @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ sk_A @ 
% 0.21/0.51           (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51            (sk_D @ sk_C @ sk_A @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['91', '92', '93', '94', '95', '96', '97'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (r1_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.21/0.51          | (m1_connsp_2 @ (sk_F @ X5 @ X1 @ X3 @ X0 @ X2) @ X2 @ X1)
% 0.21/0.51          | ~ (m1_connsp_2 @ X5 @ X0 @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.21/0.51          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (v1_funct_1 @ X3)
% 0.21/0.51          | ~ (l1_pre_topc @ X2)
% 0.21/0.51          | ~ (v2_pre_topc @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tmap_1])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | (m1_connsp_2 @ (sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B) @ sk_B @ X0)
% 0.21/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.51  thf('102', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | (m1_connsp_2 @ (sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B) @ sk_B @ X0)
% 0.21/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['101', '102', '103', '104', '105', '106', '107'])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | (m1_connsp_2 @ 
% 0.21/0.51           (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51            (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51           sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['98', '108'])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (((m1_connsp_2 @ 
% 0.21/0.51         (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ (sk_D @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51          sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51         sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (m1_connsp_2 @ 
% 0.21/0.51           (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51            (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51           sk_B @ (sk_D @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '110'])).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      (((m1_connsp_2 @ 
% 0.21/0.51         (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ (sk_D @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51          sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51         sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('simplify', [status(thm)], ['111'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (m1_connsp_2 @ 
% 0.21/0.51           (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51            (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51           sk_B @ (sk_D @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['82', '112'])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (((m1_connsp_2 @ 
% 0.21/0.51         (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ (sk_D @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51          sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51         sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['113'])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['75', '76', '77', '78', '79', '80', '81'])).
% 0.21/0.51  thf('116', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['85', '87'])).
% 0.21/0.51  thf('117', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (m1_connsp_2 @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ sk_A @ 
% 0.21/0.51           (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51            (sk_D @ sk_C @ sk_A @ sk_B)))
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['91', '92', '93', '94', '95', '96', '97'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('119', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X2))
% 0.21/0.51          | ~ (r1_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.21/0.51          | (r1_tarski @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 0.21/0.51              (sk_F @ X5 @ X1 @ X3 @ X0 @ X2)) @ 
% 0.21/0.51             X5)
% 0.21/0.51          | ~ (m1_connsp_2 @ X5 @ X0 @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ X1))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.21/0.51          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (v1_funct_1 @ X3)
% 0.21/0.51          | ~ (l1_pre_topc @ X2)
% 0.21/0.51          | ~ (v2_pre_topc @ X2)
% 0.21/0.51          | (v2_struct_0 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_tmap_1])).
% 0.21/0.51  thf('120', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | (r1_tarski @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              sk_C @ (sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['118', '119'])).
% 0.21/0.51  thf('121', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('122', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('124', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('127', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_connsp_2 @ X1 @ sk_A @ 
% 0.21/0.51               (k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51                sk_C @ X0))
% 0.21/0.51          | (r1_tarski @ 
% 0.21/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.51              sk_C @ (sk_F @ X1 @ X0 @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['120', '121', '122', '123', '124', '125', '126'])).
% 0.21/0.51  thf('128', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | (r1_tarski @ 
% 0.21/0.51           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51            (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51             (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51           (sk_E_1 @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['117', '127'])).
% 0.21/0.51  thf('129', plain,
% 0.21/0.51      (((r1_tarski @ 
% 0.21/0.51         (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51          (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51           (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51         (sk_E_1 @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('simplify', [status(thm)], ['128'])).
% 0.21/0.51  thf('130', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (r1_tarski @ 
% 0.21/0.51           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51            (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51             (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51           (sk_E_1 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['116', '129'])).
% 0.21/0.51  thf('131', plain,
% 0.21/0.51      (((r1_tarski @ 
% 0.21/0.51         (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.51          (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.51           (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.51         (sk_E_1 @ sk_C @ sk_A @ sk_B))
% 0.21/0.51        | ~ (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | (v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('simplify', [status(thm)], ['130'])).
% 0.21/0.51  thf('132', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.51        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (r1_tarski @ 
% 0.21/0.52           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.52            (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52             (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.52           (sk_E_1 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['115', '131'])).
% 0.21/0.52  thf('133', plain,
% 0.21/0.52      (((r1_tarski @ 
% 0.21/0.52         (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.52          (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52           (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B)) @ 
% 0.21/0.52         (sk_E_1 @ sk_C @ sk_A @ sk_B))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['132'])).
% 0.21/0.52  thf('134', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X6)
% 0.21/0.52          | ~ (v2_pre_topc @ X6)
% 0.21/0.52          | ~ (l1_pre_topc @ X6)
% 0.21/0.52          | ~ (m1_connsp_2 @ X11 @ X8 @ (sk_D @ X7 @ X6 @ X8))
% 0.21/0.52          | ~ (r1_tarski @ 
% 0.21/0.52               (k7_relset_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6) @ X7 @ 
% 0.21/0.52                X11) @ 
% 0.21/0.52               (sk_E_1 @ X7 @ X6 @ X8))
% 0.21/0.52          | (v5_pre_topc @ X7 @ X8 @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.52               (k1_zfmisc_1 @ 
% 0.21/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.21/0.52          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.21/0.52          | ~ (v1_funct_1 @ X7)
% 0.21/0.52          | ~ (l1_pre_topc @ X8)
% 0.21/0.52          | ~ (v2_pre_topc @ X8)
% 0.21/0.52          | (v2_struct_0 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_borsuk_1])).
% 0.21/0.52  thf('135', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (m1_subset_1 @ sk_C @ 
% 0.21/0.52             (k1_zfmisc_1 @ 
% 0.21/0.52              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | ~ (m1_connsp_2 @ 
% 0.21/0.52             (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52              (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52             sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['133', '134'])).
% 0.21/0.52  thf('136', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('137', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('139', plain,
% 0.21/0.52      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('140', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ 
% 0.21/0.52        (k1_zfmisc_1 @ 
% 0.21/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('143', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | ~ (m1_connsp_2 @ 
% 0.21/0.52             (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52              (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52             sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['135', '136', '137', '138', '139', '140', '141', '142'])).
% 0.21/0.52  thf('144', plain,
% 0.21/0.52      ((~ (m1_connsp_2 @ 
% 0.21/0.52           (sk_F @ (sk_E_1 @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52            (sk_D @ sk_C @ sk_A @ sk_B) @ sk_C @ sk_A @ sk_B) @ 
% 0.21/0.52           sk_B @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['143'])).
% 0.21/0.52  thf('145', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_B)
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['114', '144'])).
% 0.21/0.52  thf('146', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_B)
% 0.21/0.52        | (v5_pre_topc @ sk_C @ sk_B @ sk_A)
% 0.21/0.52        | (v2_struct_0 @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['145'])).
% 0.21/0.52  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('148', plain,
% 0.21/0.52      (((v2_struct_0 @ sk_A) | (v5_pre_topc @ sk_C @ sk_B @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['146', '147'])).
% 0.21/0.52  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('150', plain, ((v5_pre_topc @ sk_C @ sk_B @ sk_A)),
% 0.21/0.52      inference('clc', [status(thm)], ['148', '149'])).
% 0.21/0.52  thf('151', plain, ($false), inference('demod', [status(thm)], ['72', '150'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
