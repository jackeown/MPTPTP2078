%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OiuwFYIBsC

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:32 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 196 expanded)
%              Number of leaves         :   30 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          : 1200 (5402 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_connsp_1_type,type,(
    v2_connsp_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t76_tops_2,conjecture,(
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
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_tops_2 @ C @ A @ B )
                      & ( v2_connsp_1 @ D @ B ) )
                   => ( v2_connsp_1 @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) )).

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
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( v3_tops_2 @ C @ A @ B )
                        & ( v2_connsp_1 @ D @ B ) )
                     => ( v2_connsp_1 @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_2])).

thf('0',plain,(
    ~ ( v2_connsp_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X4 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t75_tops_2,axiom,(
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
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v5_pre_topc @ C @ A @ B )
                      & ( v2_connsp_1 @ D @ A ) )
                   => ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ X12 ) @ X11 )
      | ~ ( v2_connsp_1 @ X12 @ X13 )
      | ~ ( v5_pre_topc @ X14 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t75_tops_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v2_connsp_1 @ X0 @ sk_B )
      | ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X4 @ X5 @ X6 ) @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v3_tops_2 @ X2 @ X3 @ X1 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 ) @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_connsp_1 @ X0 @ sk_B )
      | ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','17','23','32','33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) @ sk_A )
    | ~ ( v2_connsp_1 @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    v2_connsp_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) @ sk_A ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t68_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X10 @ X8 )
        = ( k7_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X9 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X10 ) @ X8 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X10 )
       != ( k2_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t68_tops_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v3_tops_2 @ X2 @ X3 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 )
        = ( k2_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v3_tops_2 @ X2 @ X3 @ X1 )
      | ( v2_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64','65','66','67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['46','49','50','51','60','69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
    = ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['43','74'])).

thf('76',plain,(
    v2_connsp_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['42','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OiuwFYIBsC
% 0.17/0.38  % Computer   : n010.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 10:02:15 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 90 iterations in 0.111s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.61  thf(v2_connsp_1_type, type, v2_connsp_1: $i > $i > $o).
% 0.41/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.61  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.41/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.61  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.61  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.41/0.61  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.41/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(t76_tops_2, conjecture,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61             ( l1_pre_topc @ B ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                 ( m1_subset_1 @
% 0.41/0.61                   C @ 
% 0.41/0.61                   ( k1_zfmisc_1 @
% 0.41/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.61                   ( ( ( v3_tops_2 @ C @ A @ B ) & ( v2_connsp_1 @ D @ B ) ) =>
% 0.41/0.61                     ( v2_connsp_1 @
% 0.41/0.61                       ( k8_relset_1 @
% 0.41/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.41/0.61                       A ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i]:
% 0.41/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.61            ( l1_pre_topc @ A ) ) =>
% 0.41/0.61          ( ![B:$i]:
% 0.41/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61                ( l1_pre_topc @ B ) ) =>
% 0.41/0.61              ( ![C:$i]:
% 0.41/0.61                ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61                    ( v1_funct_2 @
% 0.41/0.61                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                    ( m1_subset_1 @
% 0.41/0.61                      C @ 
% 0.41/0.61                      ( k1_zfmisc_1 @
% 0.41/0.61                        ( k2_zfmisc_1 @
% 0.41/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61                  ( ![D:$i]:
% 0.41/0.61                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.61                      ( ( ( v3_tops_2 @ C @ A @ B ) & ( v2_connsp_1 @ D @ B ) ) =>
% 0.41/0.61                        ( v2_connsp_1 @
% 0.41/0.61                          ( k8_relset_1 @
% 0.41/0.61                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.41/0.61                          A ) ) ) ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t76_tops_2])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (~ (v2_connsp_1 @ 
% 0.41/0.61          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.41/0.61           sk_D) @ 
% 0.41/0.61          sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_k2_tops_2, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.41/0.61         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.41/0.61         ( m1_subset_1 @
% 0.41/0.61           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.41/0.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.61         ((m1_subset_1 @ (k2_tops_2 @ X4 @ X5 @ X6) @ 
% 0.41/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X4)))
% 0.41/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.41/0.61          | ~ (v1_funct_2 @ X6 @ X4 @ X5)
% 0.41/0.61          | ~ (v1_funct_1 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | (m1_subset_1 @ 
% 0.41/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61           (k1_zfmisc_1 @ 
% 0.41/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.61  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      ((m1_subset_1 @ 
% 0.41/0.61        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.41/0.61  thf(t75_tops_2, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61             ( l1_pre_topc @ B ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                 ( m1_subset_1 @
% 0.41/0.61                   C @ 
% 0.41/0.61                   ( k1_zfmisc_1 @
% 0.41/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61                   ( ( ( v5_pre_topc @ C @ A @ B ) & ( v2_connsp_1 @ D @ A ) ) =>
% 0.41/0.61                     ( v2_connsp_1 @
% 0.41/0.61                       ( k7_relset_1 @
% 0.41/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.41/0.61                       B ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X11)
% 0.41/0.61          | ~ (v2_pre_topc @ X11)
% 0.41/0.61          | ~ (l1_pre_topc @ X11)
% 0.41/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.41/0.61          | (v2_connsp_1 @ 
% 0.41/0.61             (k7_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X14 @ 
% 0.41/0.61              X12) @ 
% 0.41/0.61             X11)
% 0.41/0.61          | ~ (v2_connsp_1 @ X12 @ X13)
% 0.41/0.61          | ~ (v5_pre_topc @ X14 @ X13 @ X11)
% 0.41/0.61          | ~ (m1_subset_1 @ X14 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.41/0.61          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.41/0.61          | ~ (v1_funct_1 @ X14)
% 0.41/0.61          | ~ (l1_pre_topc @ X13)
% 0.41/0.61          | ~ (v2_pre_topc @ X13)
% 0.41/0.61          | (v2_struct_0 @ X13))),
% 0.41/0.61      inference('cnf', [status(esa)], [t75_tops_2])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | ~ (v1_funct_1 @ 
% 0.41/0.61               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.61          | ~ (v1_funct_2 @ 
% 0.41/0.61               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (v5_pre_topc @ 
% 0.41/0.61               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61               sk_B @ sk_A)
% 0.41/0.61          | ~ (v2_connsp_1 @ X0 @ sk_B)
% 0.41/0.61          | (v2_connsp_1 @ 
% 0.41/0.61             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61              X0) @ 
% 0.41/0.61             sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.61         ((v1_funct_1 @ (k2_tops_2 @ X4 @ X5 @ X6))
% 0.41/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.41/0.61          | ~ (v1_funct_2 @ X6 @ X4 @ X5)
% 0.41/0.61          | ~ (v1_funct_1 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | (v1_funct_1 @ 
% 0.41/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.61  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      ((v1_funct_1 @ 
% 0.41/0.61        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.61         ((v1_funct_2 @ (k2_tops_2 @ X4 @ X5 @ X6) @ X5 @ X4)
% 0.41/0.61          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.41/0.61          | ~ (v1_funct_2 @ X6 @ X4 @ X5)
% 0.41/0.61          | ~ (v1_funct_1 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | (v1_funct_2 @ 
% 0.41/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.61  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      ((v1_funct_2 @ 
% 0.41/0.61        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d5_tops_2, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_pre_topc @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( l1_pre_topc @ B ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                 ( m1_subset_1 @
% 0.41/0.61                   C @ 
% 0.41/0.61                   ( k1_zfmisc_1 @
% 0.41/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.41/0.61                 ( ( ( k1_relset_1 @
% 0.41/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.61                     ( k2_struct_0 @ A ) ) & 
% 0.41/0.61                   ( ( k2_relset_1 @
% 0.41/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.41/0.61                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.41/0.61                   ( v5_pre_topc @
% 0.41/0.61                     ( k2_tops_2 @
% 0.41/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.41/0.61                     B @ A ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X1)
% 0.41/0.61          | ~ (v3_tops_2 @ X2 @ X3 @ X1)
% 0.41/0.61          | (v5_pre_topc @ 
% 0.41/0.61             (k2_tops_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2) @ X1 @ 
% 0.41/0.61             X3)
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.41/0.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.41/0.61          | ~ (v1_funct_1 @ X2)
% 0.41/0.61          | ~ (l1_pre_topc @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | (v5_pre_topc @ 
% 0.41/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61           sk_B @ sk_A)
% 0.41/0.61        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('30', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      ((v5_pre_topc @ 
% 0.41/0.61        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61        sk_B @ sk_A)),
% 0.41/0.61      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.41/0.61  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (v2_connsp_1 @ X0 @ sk_B)
% 0.41/0.61          | (v2_connsp_1 @ 
% 0.41/0.61             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61              X0) @ 
% 0.41/0.61             sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['9', '10', '11', '17', '23', '32', '33', '34'])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | (v2_connsp_1 @ 
% 0.41/0.61           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61            sk_D) @ 
% 0.41/0.61           sk_A)
% 0.41/0.61        | ~ (v2_connsp_1 @ sk_D @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '35'])).
% 0.41/0.61  thf('37', plain, ((v2_connsp_1 @ sk_D @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A)
% 0.41/0.61        | (v2_connsp_1 @ 
% 0.41/0.61           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61            sk_D) @ 
% 0.41/0.61           sk_A)
% 0.41/0.61        | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | (v2_connsp_1 @ 
% 0.41/0.61           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61            sk_D) @ 
% 0.41/0.61           sk_A))),
% 0.41/0.61      inference('clc', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      ((v2_connsp_1 @ 
% 0.41/0.61        (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.61         sk_D) @ 
% 0.41/0.61        sk_A)),
% 0.41/0.61      inference('clc', [status(thm)], ['40', '41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t68_tops_2, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_struct_0 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( l1_struct_0 @ B ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                 ( m1_subset_1 @
% 0.41/0.61                   C @ 
% 0.41/0.61                   ( k1_zfmisc_1 @
% 0.41/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.61                   ( ( ( ( k2_relset_1 @
% 0.41/0.61                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.61                         ( k2_struct_0 @ B ) ) & 
% 0.41/0.61                       ( v2_funct_1 @ C ) ) =>
% 0.41/0.61                     ( ( k8_relset_1 @
% 0.41/0.61                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.41/0.61                       ( k7_relset_1 @
% 0.41/0.61                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.61                         ( k2_tops_2 @
% 0.41/0.61                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.41/0.61                         D ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.61         (~ (l1_struct_0 @ X7)
% 0.41/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.41/0.61          | ((k8_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X10 @ X8)
% 0.41/0.61              = (k7_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X9) @ 
% 0.41/0.61                 (k2_tops_2 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X10) @ 
% 0.41/0.61                 X8))
% 0.41/0.61          | ~ (v2_funct_1 @ X10)
% 0.41/0.61          | ((k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X10)
% 0.41/0.61              != (k2_struct_0 @ X7))
% 0.41/0.61          | ~ (m1_subset_1 @ X10 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.41/0.61          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.41/0.61          | ~ (v1_funct_1 @ X10)
% 0.41/0.61          | ~ (l1_struct_0 @ X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [t68_tops_2])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (l1_struct_0 @ sk_A)
% 0.41/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.61          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.61              != (k2_struct_0 @ sk_B))
% 0.41/0.61          | ~ (v2_funct_1 @ sk_C)
% 0.41/0.61          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61              sk_C @ X0)
% 0.41/0.61              = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61                  sk_C) @ 
% 0.41/0.61                 X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.61  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_l1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.61  thf('48', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.61  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X1)
% 0.41/0.61          | ~ (v3_tops_2 @ X2 @ X3 @ X1)
% 0.41/0.61          | ((k2_relset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1) @ X2)
% 0.41/0.61              = (k2_struct_0 @ X1))
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.41/0.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.41/0.61          | ~ (v1_funct_1 @ X2)
% 0.41/0.61          | ~ (l1_pre_topc @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.61            = (k2_struct_0 @ sk_B))
% 0.41/0.61        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('58', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('60', plain,
% 0.41/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.61         = (k2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['54', '55', '56', '57', '58', '59'])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.61         (~ (l1_pre_topc @ X1)
% 0.41/0.61          | ~ (v3_tops_2 @ X2 @ X3 @ X1)
% 0.41/0.61          | (v2_funct_1 @ X2)
% 0.41/0.61          | ~ (m1_subset_1 @ X2 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))))
% 0.41/0.61          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X1))
% 0.41/0.61          | ~ (v1_funct_1 @ X2)
% 0.41/0.61          | ~ (l1_pre_topc @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | (v2_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.41/0.61        | ~ (l1_pre_topc @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.41/0.61  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('67', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.61      inference('demod', [status(thm)], ['63', '64', '65', '66', '67', '68'])).
% 0.41/0.61  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('71', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.41/0.61          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61              sk_C @ X0)
% 0.41/0.61              = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.61                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61                  sk_C) @ 
% 0.41/0.61                 X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('demod', [status(thm)],
% 0.41/0.61                ['46', '49', '50', '51', '60', '69', '72'])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.41/0.61          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61              sk_C @ X0)
% 0.41/0.61              = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.62                  sk_C) @ 
% 0.41/0.62                 X0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['73'])).
% 0.41/0.62  thf('75', plain,
% 0.41/0.62      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.41/0.62         sk_D)
% 0.41/0.62         = (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.41/0.62            sk_D))),
% 0.41/0.62      inference('sup-', [status(thm)], ['43', '74'])).
% 0.41/0.62  thf('76', plain,
% 0.41/0.62      ((v2_connsp_1 @ 
% 0.41/0.62        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.41/0.62         sk_D) @ 
% 0.41/0.62        sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['42', '75'])).
% 0.41/0.62  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
