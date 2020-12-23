%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8b4jgFNZHy

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:42 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 411 expanded)
%              Number of leaves         :   33 ( 142 expanded)
%              Depth                    :   13
%              Number of atoms          : 1796 (14043 expanded)
%              Number of equality atoms :   31 ( 419 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(t26_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( v1_compts_1 @ A )
                  & ( v8_pre_topc @ B )
                  & ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ( v5_pre_topc @ C @ A @ B ) )
               => ( v3_tops_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( v1_compts_1 @ A )
                    & ( v8_pre_topc @ B )
                    & ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ A ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C )
                    & ( v5_pre_topc @ C @ A @ B ) )
                 => ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_compts_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 )
       != ( k2_struct_0 @ X7 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 )
       != ( k2_struct_0 @ X5 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 ) @ X5 @ X7 )
      | ( v3_tops_2 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7','8','9','10'])).

thf('12',plain,
    ( ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v5_pre_topc @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','29','35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k8_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ X12 )
        = ( k8_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 ) @ X12 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 )
       != ( k2_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t67_tops_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('42',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['40','43','44','45','46','47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
      = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','52'])).

thf('54',plain,(
    ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('55',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( sk_D @ X1 @ X0 @ X2 ) ) @ X2 )
      | ( v5_pre_topc @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('57',plain,
    ( ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( sk_D @ X1 @ X0 @ X2 ) @ X0 )
      | ( v5_pre_topc @ X1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('63',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','29','35','36'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( v1_compts_1 @ A )
                  & ( v8_pre_topc @ B )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( v4_pre_topc @ D @ A )
                     => ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_compts_1 @ X16 )
      | ~ ( v8_pre_topc @ X15 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) @ X17 )
       != ( k2_struct_0 @ X15 ) )
      | ~ ( v5_pre_topc @ X17 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) @ X17 @ X18 ) @ X15 )
      | ~ ( v4_pre_topc @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t25_compts_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73','74','75','76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','81'])).

thf('83',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','82'])).

thf('84',plain,
    ( ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('88',plain,(
    v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('91',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['57','88','89','90','91','92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['14','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8b4jgFNZHy
% 0.16/0.37  % Computer   : n014.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:52:37 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 100 iterations in 0.107s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.40/0.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.40/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.40/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.59  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.40/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.59  thf(t26_compts_1, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.59             ( l1_pre_topc @ B ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.40/0.59                   ( ( k1_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ A ) ) & 
% 0.40/0.59                   ( ( k2_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.40/0.59                 ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.59                ( l1_pre_topc @ B ) ) =>
% 0.40/0.59              ( ![C:$i]:
% 0.40/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                    ( v1_funct_2 @
% 0.40/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                    ( m1_subset_1 @
% 0.40/0.59                      C @ 
% 0.40/0.59                      ( k1_zfmisc_1 @
% 0.40/0.59                        ( k2_zfmisc_1 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.40/0.59                      ( ( k1_relset_1 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                        ( k2_struct_0 @ A ) ) & 
% 0.40/0.59                      ( ( k2_relset_1 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                        ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                      ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.40/0.59                    ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t26_compts_1])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d5_tops_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( l1_pre_topc @ B ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.40/0.59                 ( ( ( k1_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ A ) ) & 
% 0.40/0.59                   ( ( k2_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.40/0.59                   ( v5_pre_topc @
% 0.40/0.59                     ( k2_tops_2 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.40/0.59                     B @ A ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X5)
% 0.40/0.59          | ((k1_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6)
% 0.40/0.59              != (k2_struct_0 @ X7))
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6)
% 0.40/0.59              != (k2_struct_0 @ X5))
% 0.40/0.59          | ~ (v2_funct_1 @ X6)
% 0.40/0.59          | ~ (v5_pre_topc @ X6 @ X7 @ X5)
% 0.40/0.59          | ~ (v5_pre_topc @ 
% 0.40/0.59               (k2_tops_2 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6) @ 
% 0.40/0.59               X5 @ X7)
% 0.40/0.59          | (v3_tops_2 @ X6 @ X7 @ X5)
% 0.40/0.59          | ~ (m1_subset_1 @ X6 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.40/0.59          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.40/0.59          | ~ (v1_funct_1 @ X6)
% 0.40/0.59          | ~ (l1_pre_topc @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             sk_B @ sk_A)
% 0.40/0.59        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (k2_struct_0 @ sk_A))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('6', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('7', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             sk_B @ sk_A)
% 0.40/0.59        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['2', '3', '4', '5', '6', '7', '8', '9', '10'])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      ((~ (v5_pre_topc @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_B @ sk_A)
% 0.40/0.59        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.40/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.40/0.59  thf('13', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (~ (v5_pre_topc @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59          sk_B @ sk_A)),
% 0.40/0.59      inference('clc', [status(thm)], ['12', '13'])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_k2_tops_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.40/0.59         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.40/0.59         ( m1_subset_1 @
% 0.40/0.59           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.40/0.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((m1_subset_1 @ (k2_tops_2 @ X8 @ X9 @ X10) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.59          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.59          | ~ (v1_funct_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (m1_subset_1 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           (k1_zfmisc_1 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.59  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      ((m1_subset_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.40/0.59  thf(d12_pre_topc, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( l1_pre_topc @ B ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.40/0.59                 ( ![D:$i]:
% 0.40/0.59                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.40/0.59                     ( ( v4_pre_topc @ D @ B ) =>
% 0.40/0.59                       ( v4_pre_topc @
% 0.40/0.59                         ( k8_relset_1 @
% 0.40/0.59                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.40/0.59                         A ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X0)
% 0.40/0.59          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ 
% 0.40/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.40/0.59          | (v5_pre_topc @ X1 @ X2 @ X0)
% 0.40/0.59          | ~ (m1_subset_1 @ X1 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.40/0.59          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ X1)
% 0.40/0.59          | ~ (l1_pre_topc @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_B @ sk_A)
% 0.40/0.59        | (m1_subset_1 @ 
% 0.40/0.59           (sk_D @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59            sk_A @ sk_B) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((v1_funct_1 @ (k2_tops_2 @ X8 @ X9 @ X10))
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.59          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.59          | ~ (v1_funct_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v1_funct_1 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.59  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      ((v1_funct_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((v1_funct_2 @ (k2_tops_2 @ X8 @ X9 @ X10) @ X9 @ X8)
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.59          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.59          | ~ (v1_funct_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v1_funct_2 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      ((v1_funct_2 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.40/0.59  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (((v5_pre_topc @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59         sk_B @ sk_A)
% 0.40/0.59        | (m1_subset_1 @ 
% 0.40/0.59           (sk_D @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59            sk_A @ sk_B) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['22', '23', '29', '35', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t67_tops_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_struct_0 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( l1_struct_0 @ B ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ![D:$i]:
% 0.40/0.59                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.59                   ( ( ( ( k2_relset_1 @
% 0.40/0.59                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                         ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                       ( v2_funct_1 @ C ) ) =>
% 0.40/0.59                     ( ( k7_relset_1 @
% 0.40/0.59                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.40/0.59                       ( k8_relset_1 @
% 0.40/0.59                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                         ( k2_tops_2 @
% 0.40/0.59                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.40/0.59                         D ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X11)
% 0.40/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.40/0.59          | ((k7_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X14 @ 
% 0.40/0.59              X12)
% 0.40/0.59              = (k8_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13) @ 
% 0.40/0.59                 (k2_tops_2 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X14) @ 
% 0.40/0.59                 X12))
% 0.40/0.59          | ~ (v2_funct_1 @ X14)
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X14)
% 0.40/0.59              != (k2_struct_0 @ X11))
% 0.40/0.59          | ~ (m1_subset_1 @ X14 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.40/0.59          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.40/0.59          | ~ (v1_funct_1 @ X14)
% 0.40/0.59          | ~ (l1_struct_0 @ X13))),
% 0.40/0.59      inference('cnf', [status(esa)], [t67_tops_2])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ sk_A)
% 0.40/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59              != (k2_struct_0 @ sk_B))
% 0.40/0.59          | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59              sk_C @ X0)
% 0.40/0.59              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59                  sk_C) @ 
% 0.40/0.59                 X0))
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59          | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.59  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_l1_pre_topc, axiom,
% 0.40/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.59  thf('42', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.59  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('49', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.59  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.59          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59              sk_C @ X0)
% 0.40/0.59              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59                  sk_C) @ 
% 0.40/0.59                 X0))
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['40', '43', '44', '45', '46', '47', '50'])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.59          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59              sk_C @ X0)
% 0.40/0.59              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59                  sk_C) @ 
% 0.40/0.59                 X0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (((v5_pre_topc @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59         sk_B @ sk_A)
% 0.40/0.59        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.59            (sk_D @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             sk_A @ sk_B))
% 0.40/0.59            = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59               (sk_D @ 
% 0.40/0.59                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59                sk_A @ sk_B))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['37', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (~ (v5_pre_topc @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59          sk_B @ sk_A)),
% 0.40/0.59      inference('clc', [status(thm)], ['12', '13'])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.59         (sk_D @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59          sk_A @ sk_B))
% 0.40/0.59         = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59            (sk_D @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             sk_A @ sk_B)))),
% 0.40/0.59      inference('clc', [status(thm)], ['53', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X0)
% 0.40/0.59          | ~ (v4_pre_topc @ 
% 0.40/0.59               (k8_relset_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.40/0.59                (sk_D @ X1 @ X0 @ X2)) @ 
% 0.40/0.59               X2)
% 0.40/0.59          | (v5_pre_topc @ X1 @ X2 @ X0)
% 0.40/0.59          | ~ (m1_subset_1 @ X1 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.40/0.59          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ X1)
% 0.40/0.59          | ~ (l1_pre_topc @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      ((~ (v4_pre_topc @ 
% 0.40/0.59           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.59            (sk_D @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             sk_A @ sk_B)) @ 
% 0.40/0.59           sk_B)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | ~ (m1_subset_1 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             (k1_zfmisc_1 @ 
% 0.40/0.59              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_B @ sk_A)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      ((m1_subset_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X0)
% 0.40/0.59          | (v4_pre_topc @ (sk_D @ X1 @ X0 @ X2) @ X0)
% 0.40/0.59          | (v5_pre_topc @ X1 @ X2 @ X0)
% 0.40/0.59          | ~ (m1_subset_1 @ X1 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.40/0.59          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.40/0.59          | ~ (v1_funct_1 @ X1)
% 0.40/0.59          | ~ (l1_pre_topc @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_B @ sk_A)
% 0.40/0.59        | (v4_pre_topc @ 
% 0.40/0.59           (sk_D @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59            sk_A @ sk_B) @ 
% 0.40/0.59           sk_A)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.59  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      ((v1_funct_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      ((v1_funct_2 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.40/0.59  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      (((v5_pre_topc @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60         sk_B @ sk_A)
% 0.40/0.60        | (v4_pre_topc @ 
% 0.40/0.60           (sk_D @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60            sk_A @ sk_B) @ 
% 0.40/0.60           sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      (((v5_pre_topc @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60         sk_B @ sk_A)
% 0.40/0.60        | (m1_subset_1 @ 
% 0.40/0.60           (sk_D @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60            sk_A @ sk_B) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['22', '23', '29', '35', '36'])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t25_compts_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.60             ( l1_pre_topc @ B ) ) =>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.60                 ( m1_subset_1 @
% 0.40/0.60                   C @ 
% 0.40/0.60                   ( k1_zfmisc_1 @
% 0.40/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.60               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.40/0.60                   ( ( k2_relset_1 @
% 0.40/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.60                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.40/0.60                 ( ![D:$i]:
% 0.40/0.60                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60                     ( ( v4_pre_topc @ D @ A ) =>
% 0.40/0.60                       ( v4_pre_topc @
% 0.40/0.60                         ( k7_relset_1 @
% 0.40/0.60                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.40/0.60                         B ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.60         ((v2_struct_0 @ X15)
% 0.40/0.60          | ~ (v2_pre_topc @ X15)
% 0.40/0.60          | ~ (l1_pre_topc @ X15)
% 0.40/0.60          | ~ (v1_compts_1 @ X16)
% 0.40/0.60          | ~ (v8_pre_topc @ X15)
% 0.40/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17)
% 0.40/0.60              != (k2_struct_0 @ X15))
% 0.40/0.60          | ~ (v5_pre_topc @ X17 @ X16 @ X15)
% 0.40/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.40/0.60          | (v4_pre_topc @ 
% 0.40/0.60             (k7_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17 @ 
% 0.40/0.60              X18) @ 
% 0.40/0.60             X15)
% 0.40/0.60          | ~ (v4_pre_topc @ X18 @ X16)
% 0.40/0.60          | ~ (m1_subset_1 @ X17 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))))
% 0.40/0.60          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.40/0.60          | ~ (v1_funct_1 @ X17)
% 0.40/0.60          | ~ (l1_pre_topc @ X16)
% 0.40/0.60          | ~ (v2_pre_topc @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [t25_compts_1])).
% 0.40/0.60  thf('69', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v2_pre_topc @ sk_A)
% 0.40/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.60          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (v4_pre_topc @ 
% 0.40/0.60             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60              sk_C @ X0) @ 
% 0.40/0.60             sk_B)
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.60          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.40/0.60          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60              != (k2_struct_0 @ sk_B))
% 0.40/0.60          | ~ (v8_pre_topc @ sk_B)
% 0.40/0.60          | ~ (v1_compts_1 @ sk_A)
% 0.40/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.40/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['67', '68'])).
% 0.40/0.60  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('73', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('74', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.60         = (k2_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('76', plain, ((v8_pre_topc @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('77', plain, ((v1_compts_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('80', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v4_pre_topc @ X0 @ sk_A)
% 0.40/0.60          | (v4_pre_topc @ 
% 0.40/0.60             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60              sk_C @ X0) @ 
% 0.40/0.60             sk_B)
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.60          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.60          | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)],
% 0.40/0.60                ['69', '70', '71', '72', '73', '74', '75', '76', '77', '78', 
% 0.40/0.60                 '79'])).
% 0.40/0.60  thf('81', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((v2_struct_0 @ sk_B)
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.60          | (v4_pre_topc @ 
% 0.40/0.60             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60              sk_C @ X0) @ 
% 0.40/0.60             sk_B)
% 0.40/0.60          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['80'])).
% 0.40/0.60  thf('82', plain,
% 0.40/0.60      (((v5_pre_topc @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60         sk_B @ sk_A)
% 0.40/0.60        | ~ (v4_pre_topc @ 
% 0.40/0.60             (sk_D @ 
% 0.40/0.60              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60              sk_A @ sk_B) @ 
% 0.40/0.60             sk_A)
% 0.40/0.60        | (v4_pre_topc @ 
% 0.40/0.60           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.60            (sk_D @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60             sk_A @ sk_B)) @ 
% 0.40/0.60           sk_B)
% 0.40/0.60        | (v2_struct_0 @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['66', '81'])).
% 0.40/0.60  thf('83', plain,
% 0.40/0.60      (((v5_pre_topc @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60         sk_B @ sk_A)
% 0.40/0.60        | (v2_struct_0 @ sk_B)
% 0.40/0.60        | (v4_pre_topc @ 
% 0.40/0.60           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.60            (sk_D @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60             sk_A @ sk_B)) @ 
% 0.40/0.60           sk_B)
% 0.40/0.60        | (v5_pre_topc @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60           sk_B @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['65', '82'])).
% 0.40/0.60  thf('84', plain,
% 0.40/0.60      (((v4_pre_topc @ 
% 0.40/0.60         (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.60          (sk_D @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60           sk_A @ sk_B)) @ 
% 0.40/0.60         sk_B)
% 0.40/0.60        | (v2_struct_0 @ sk_B)
% 0.40/0.60        | (v5_pre_topc @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60           sk_B @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['83'])).
% 0.40/0.60  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('86', plain,
% 0.40/0.60      (((v5_pre_topc @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60         sk_B @ sk_A)
% 0.40/0.60        | (v4_pre_topc @ 
% 0.40/0.60           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.60            (sk_D @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60             sk_A @ sk_B)) @ 
% 0.40/0.60           sk_B))),
% 0.40/0.60      inference('clc', [status(thm)], ['84', '85'])).
% 0.40/0.60  thf('87', plain,
% 0.40/0.60      (~ (v5_pre_topc @ 
% 0.40/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60          sk_B @ sk_A)),
% 0.40/0.60      inference('clc', [status(thm)], ['12', '13'])).
% 0.40/0.60  thf('88', plain,
% 0.40/0.60      ((v4_pre_topc @ 
% 0.40/0.60        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.60         (sk_D @ 
% 0.40/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60          sk_A @ sk_B)) @ 
% 0.40/0.60        sk_B)),
% 0.40/0.60      inference('clc', [status(thm)], ['86', '87'])).
% 0.40/0.60  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('90', plain,
% 0.40/0.60      ((v1_funct_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.60      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.40/0.60  thf('91', plain,
% 0.40/0.60      ((v1_funct_2 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.40/0.60  thf('92', plain,
% 0.40/0.60      ((m1_subset_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.40/0.60  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('94', plain,
% 0.40/0.60      ((v5_pre_topc @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        sk_B @ sk_A)),
% 0.40/0.60      inference('demod', [status(thm)],
% 0.40/0.60                ['57', '88', '89', '90', '91', '92', '93'])).
% 0.40/0.60  thf('95', plain, ($false), inference('demod', [status(thm)], ['14', '94'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
