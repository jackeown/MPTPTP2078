%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zjZFSnmyI

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 480 expanded)
%              Number of leaves         :   37 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          : 2052 (16218 expanded)
%              Number of equality atoms :   31 ( 471 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 )
       != ( k2_struct_0 @ X11 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 )
       != ( k2_struct_0 @ X9 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v5_pre_topc @ X10 @ X11 @ X9 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 ) @ X9 @ X11 )
      | ( v3_tops_2 @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X12 @ X13 @ X14 ) @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ X18 @ X16 )
        = ( k8_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ X18 ) @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ X18 )
       != ( k2_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
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
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X5 @ ( sk_D @ X5 @ X4 @ X6 ) ) @ X6 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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

thf('58',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','29','35','36'])).

thf(t17_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_compts_1 @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v2_compts_1 @ B @ A ) ) ) ) )).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_compts_1 @ X21 @ X22 )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ~ ( v1_compts_1 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t17_compts_1])).

thf('60',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ( v2_compts_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ( v2_compts_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('65',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ( v4_pre_topc @ ( sk_D @ X5 @ X4 @ X6 ) @ X4 )
      | ( v5_pre_topc @ X5 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('69',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( v2_compts_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['63','71'])).

thf('73',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','29','35','36'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                 => ( ( ( v5_pre_topc @ D @ A @ C )
                      & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D )
                        = ( k2_struct_0 @ C ) )
                      & ( v2_compts_1 @ B @ A ) )
                   => ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ C ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) @ X25 @ X23 ) @ X26 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) @ X25 )
       != ( k2_struct_0 @ X26 ) )
      | ~ ( v5_pre_topc @ X25 @ X24 @ X26 )
      | ~ ( v2_compts_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t24_compts_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_compts_1 @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','84'])).

thf('86',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('91',plain,(
    v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('95',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( v2_compts_1 @ X19 @ X20 )
      | ~ ( v8_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('104',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('105',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['57','101','102','103','104','105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['14','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zjZFSnmyI
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 123 iterations in 0.126s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.55  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.19/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.19/0.55  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.19/0.55  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.19/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.19/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.55  thf(t26_compts_1, conjecture,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55             ( l1_pre_topc @ B ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                 ( m1_subset_1 @
% 0.19/0.55                   C @ 
% 0.19/0.55                   ( k1_zfmisc_1 @
% 0.19/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.19/0.55                   ( ( k1_relset_1 @
% 0.19/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.55                     ( k2_struct_0 @ A ) ) & 
% 0.19/0.55                   ( ( k2_relset_1 @
% 0.19/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.19/0.55                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.19/0.55                 ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i]:
% 0.19/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55          ( ![B:$i]:
% 0.19/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.55                ( l1_pre_topc @ B ) ) =>
% 0.19/0.55              ( ![C:$i]:
% 0.19/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                    ( v1_funct_2 @
% 0.19/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                    ( m1_subset_1 @
% 0.19/0.55                      C @ 
% 0.19/0.55                      ( k1_zfmisc_1 @
% 0.19/0.55                        ( k2_zfmisc_1 @
% 0.19/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.19/0.55                      ( ( k1_relset_1 @
% 0.19/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.55                        ( k2_struct_0 @ A ) ) & 
% 0.19/0.55                      ( ( k2_relset_1 @
% 0.19/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.19/0.55                      ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.19/0.55                    ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t26_compts_1])).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d5_tops_2, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( l1_pre_topc @ B ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                 ( m1_subset_1 @
% 0.19/0.55                   C @ 
% 0.19/0.55                   ( k1_zfmisc_1 @
% 0.19/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.19/0.55                 ( ( ( k1_relset_1 @
% 0.19/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.55                     ( k2_struct_0 @ A ) ) & 
% 0.19/0.55                   ( ( k2_relset_1 @
% 0.19/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.19/0.55                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.19/0.55                   ( v5_pre_topc @
% 0.19/0.55                     ( k2_tops_2 @
% 0.19/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.19/0.55                     B @ A ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X9)
% 0.19/0.55          | ((k1_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10)
% 0.19/0.55              != (k2_struct_0 @ X11))
% 0.19/0.55          | ((k2_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10)
% 0.19/0.55              != (k2_struct_0 @ X9))
% 0.19/0.55          | ~ (v2_funct_1 @ X10)
% 0.19/0.55          | ~ (v5_pre_topc @ X10 @ X11 @ X9)
% 0.19/0.55          | ~ (v5_pre_topc @ 
% 0.19/0.55               (k2_tops_2 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10) @ 
% 0.19/0.55               X9 @ X11)
% 0.19/0.55          | (v3_tops_2 @ X10 @ X11 @ X9)
% 0.19/0.55          | ~ (m1_subset_1 @ X10 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.19/0.55          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.19/0.55          | ~ (v1_funct_1 @ X10)
% 0.19/0.55          | ~ (l1_pre_topc @ X11))),
% 0.19/0.55      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.55        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.55        | ~ (v5_pre_topc @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_B @ sk_A)
% 0.19/0.55        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.19/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.55        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55            != (k2_struct_0 @ sk_B))
% 0.19/0.55        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55            != (k2_struct_0 @ sk_A))
% 0.19/0.55        | ~ (l1_pre_topc @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.55  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('6', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('7', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55         = (k2_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55         = (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.55        | ~ (v5_pre_topc @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_B @ sk_A)
% 0.19/0.55        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.19/0.55        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)],
% 0.19/0.55                ['2', '3', '4', '5', '6', '7', '8', '9', '10'])).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      ((~ (v5_pre_topc @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           sk_B @ sk_A)
% 0.19/0.55        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.55  thf('13', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (~ (v5_pre_topc @ 
% 0.19/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55          sk_B @ sk_A)),
% 0.19/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(dt_k2_tops_2, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.55       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.19/0.55         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.19/0.55         ( m1_subset_1 @
% 0.19/0.55           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.19/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         ((m1_subset_1 @ (k2_tops_2 @ X12 @ X13 @ X14) @ 
% 0.19/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12)))
% 0.19/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.19/0.55          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.19/0.55          | ~ (v1_funct_1 @ X14))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.55        | (m1_subset_1 @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           (k1_zfmisc_1 @ 
% 0.19/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.55  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      ((m1_subset_1 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.55  thf(d12_pre_topc, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( l1_pre_topc @ B ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                 ( m1_subset_1 @
% 0.19/0.55                   C @ 
% 0.19/0.55                   ( k1_zfmisc_1 @
% 0.19/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.19/0.55                 ( ![D:$i]:
% 0.19/0.55                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.55                     ( ( v4_pre_topc @ D @ B ) =>
% 0.19/0.55                       ( v4_pre_topc @
% 0.19/0.55                         ( k8_relset_1 @
% 0.19/0.55                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.19/0.55                         A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X4)
% 0.19/0.55          | (m1_subset_1 @ (sk_D @ X5 @ X4 @ X6) @ 
% 0.19/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.55          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.19/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.19/0.55          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.19/0.55          | ~ (v1_funct_1 @ X5)
% 0.19/0.55          | ~ (l1_pre_topc @ X6))),
% 0.19/0.55      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.55        | ~ (v1_funct_1 @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.55        | ~ (v1_funct_2 @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.55        | (v5_pre_topc @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           sk_B @ sk_A)
% 0.19/0.55        | (m1_subset_1 @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.55  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         ((v1_funct_1 @ (k2_tops_2 @ X12 @ X13 @ X14))
% 0.19/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.19/0.55          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.19/0.55          | ~ (v1_funct_1 @ X14))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.55        | (v1_funct_1 @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.55  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      ((v1_funct_1 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         ((v1_funct_2 @ (k2_tops_2 @ X12 @ X13 @ X14) @ X13 @ X12)
% 0.19/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.19/0.55          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.19/0.55          | ~ (v1_funct_1 @ X14))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.55        | (v1_funct_2 @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.55  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      ((v1_funct_2 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.19/0.55  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | (m1_subset_1 @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['22', '23', '29', '35', '36'])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t67_tops_2, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_struct_0 @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( l1_struct_0 @ B ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                 ( m1_subset_1 @
% 0.19/0.55                   C @ 
% 0.19/0.55                   ( k1_zfmisc_1 @
% 0.19/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55                   ( ( ( ( k2_relset_1 @
% 0.19/0.55                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.55                         ( k2_struct_0 @ B ) ) & 
% 0.19/0.55                       ( v2_funct_1 @ C ) ) =>
% 0.19/0.55                     ( ( k7_relset_1 @
% 0.19/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.19/0.55                       ( k8_relset_1 @
% 0.19/0.55                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.55                         ( k2_tops_2 @
% 0.19/0.55                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.19/0.55                         D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.55         (~ (l1_struct_0 @ X15)
% 0.19/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.19/0.55          | ((k7_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ X18 @ 
% 0.19/0.55              X16)
% 0.19/0.55              = (k8_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X17) @ 
% 0.19/0.55                 (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ X18) @ 
% 0.19/0.55                 X16))
% 0.19/0.55          | ~ (v2_funct_1 @ X18)
% 0.19/0.55          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ X18)
% 0.19/0.55              != (k2_struct_0 @ X15))
% 0.19/0.55          | ~ (m1_subset_1 @ X18 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 0.19/0.55          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 0.19/0.55          | ~ (v1_funct_1 @ X18)
% 0.19/0.55          | ~ (l1_struct_0 @ X17))),
% 0.19/0.55      inference('cnf', [status(esa)], [t67_tops_2])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (l1_struct_0 @ sk_A)
% 0.19/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.55          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55              != (k2_struct_0 @ sk_B))
% 0.19/0.55          | ~ (v2_funct_1 @ sk_C)
% 0.19/0.55          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0)
% 0.19/0.55              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55                  sk_C) @ 
% 0.19/0.55                 X0))
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.55  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(dt_l1_pre_topc, axiom,
% 0.19/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.55  thf('42', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.55  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.55  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('45', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55         = (k2_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('49', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.55  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.55  thf('51', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.19/0.55          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0)
% 0.19/0.55              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55                  sk_C) @ 
% 0.19/0.55                 X0))
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)],
% 0.19/0.55                ['40', '43', '44', '45', '46', '47', '50'])).
% 0.19/0.55  thf('52', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0)
% 0.19/0.55              = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55                 (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55                  sk_C) @ 
% 0.19/0.55                 X0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55            (sk_D @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_A @ sk_B))
% 0.19/0.55            = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55               (sk_D @ 
% 0.19/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55                sk_A @ sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['37', '52'])).
% 0.19/0.55  thf('54', plain,
% 0.19/0.55      (~ (v5_pre_topc @ 
% 0.19/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55          sk_B @ sk_A)),
% 0.19/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.19/0.55  thf('55', plain,
% 0.19/0.55      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55         (sk_D @ 
% 0.19/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55          sk_A @ sk_B))
% 0.19/0.55         = (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            (sk_D @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_A @ sk_B)))),
% 0.19/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.19/0.55  thf('56', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X4)
% 0.19/0.55          | ~ (v4_pre_topc @ 
% 0.19/0.55               (k8_relset_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X5 @ 
% 0.19/0.55                (sk_D @ X5 @ X4 @ X6)) @ 
% 0.19/0.55               X6)
% 0.19/0.55          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.19/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.19/0.55          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.19/0.55          | ~ (v1_funct_1 @ X5)
% 0.19/0.55          | ~ (l1_pre_topc @ X6))),
% 0.19/0.55      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      ((~ (v4_pre_topc @ 
% 0.19/0.55           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55            (sk_D @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_A @ sk_B)) @ 
% 0.19/0.55           sk_B)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.19/0.55        | ~ (v1_funct_1 @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.55        | ~ (v1_funct_2 @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.55        | ~ (m1_subset_1 @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             (k1_zfmisc_1 @ 
% 0.19/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.19/0.55        | (v5_pre_topc @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           sk_B @ sk_A)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | (m1_subset_1 @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['22', '23', '29', '35', '36'])).
% 0.19/0.55  thf(t17_compts_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ( ( v1_compts_1 @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.19/0.55             ( v2_compts_1 @ B @ A ) ) ) ) ))).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      (![X21 : $i, X22 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.19/0.55          | (v2_compts_1 @ X21 @ X22)
% 0.19/0.55          | ~ (v4_pre_topc @ X21 @ X22)
% 0.19/0.55          | ~ (v1_compts_1 @ X22)
% 0.19/0.55          | ~ (l1_pre_topc @ X22))),
% 0.19/0.55      inference('cnf', [status(esa)], [t17_compts_1])).
% 0.19/0.55  thf('60', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55        | ~ (v1_compts_1 @ sk_A)
% 0.19/0.55        | ~ (v4_pre_topc @ 
% 0.19/0.55             (sk_D @ 
% 0.19/0.55              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55              sk_A @ sk_B) @ 
% 0.19/0.55             sk_A)
% 0.19/0.55        | (v2_compts_1 @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('62', plain, ((v1_compts_1 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('63', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | ~ (v4_pre_topc @ 
% 0.19/0.55             (sk_D @ 
% 0.19/0.55              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55              sk_A @ sk_B) @ 
% 0.19/0.55             sk_A)
% 0.19/0.55        | (v2_compts_1 @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.19/0.55  thf('64', plain,
% 0.19/0.55      ((m1_subset_1 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.55  thf('65', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X4)
% 0.19/0.55          | (v4_pre_topc @ (sk_D @ X5 @ X4 @ X6) @ X4)
% 0.19/0.55          | (v5_pre_topc @ X5 @ X6 @ X4)
% 0.19/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.19/0.55          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.19/0.55          | ~ (v1_funct_1 @ X5)
% 0.19/0.55          | ~ (l1_pre_topc @ X6))),
% 0.19/0.55      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.19/0.55  thf('66', plain,
% 0.19/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.55        | ~ (v1_funct_1 @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.55        | ~ (v1_funct_2 @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.19/0.55        | (v5_pre_topc @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           sk_B @ sk_A)
% 0.19/0.55        | (v4_pre_topc @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           sk_A)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.55  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('68', plain,
% 0.19/0.55      ((v1_funct_1 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.55  thf('69', plain,
% 0.19/0.55      ((v1_funct_2 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.19/0.55  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('71', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | (v4_pre_topc @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.19/0.55  thf('72', plain,
% 0.19/0.55      (((v2_compts_1 @ 
% 0.19/0.55         (sk_D @ 
% 0.19/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55          sk_A @ sk_B) @ 
% 0.19/0.55         sk_A)
% 0.19/0.55        | (v5_pre_topc @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           sk_B @ sk_A))),
% 0.19/0.55      inference('clc', [status(thm)], ['63', '71'])).
% 0.19/0.55  thf('73', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | (m1_subset_1 @ 
% 0.19/0.55           (sk_D @ 
% 0.19/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55            sk_A @ sk_B) @ 
% 0.19/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['22', '23', '29', '35', '36'])).
% 0.19/0.55  thf('74', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t24_compts_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_pre_topc @ C ) ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.19/0.55                     ( v1_funct_2 @
% 0.19/0.55                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.19/0.55                     ( m1_subset_1 @
% 0.19/0.55                       D @ 
% 0.19/0.55                       ( k1_zfmisc_1 @
% 0.19/0.55                         ( k2_zfmisc_1 @
% 0.19/0.55                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.19/0.55                   ( ( ( v5_pre_topc @ D @ A @ C ) & 
% 0.19/0.55                       ( ( k2_relset_1 @
% 0.19/0.55                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D ) =
% 0.19/0.55                         ( k2_struct_0 @ C ) ) & 
% 0.19/0.55                       ( v2_compts_1 @ B @ A ) ) =>
% 0.19/0.55                     ( v2_compts_1 @
% 0.19/0.55                       ( k7_relset_1 @
% 0.19/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ 
% 0.19/0.55                       C ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('75', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.55          | ~ (v1_funct_1 @ X25)
% 0.19/0.55          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.19/0.55          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.55               (k1_zfmisc_1 @ 
% 0.19/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))))
% 0.19/0.55          | (v2_compts_1 @ 
% 0.19/0.55             (k7_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26) @ X25 @ 
% 0.19/0.55              X23) @ 
% 0.19/0.55             X26)
% 0.19/0.55          | ((k2_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26) @ X25)
% 0.19/0.55              != (k2_struct_0 @ X26))
% 0.19/0.55          | ~ (v5_pre_topc @ X25 @ X24 @ X26)
% 0.19/0.55          | ~ (v2_compts_1 @ X23 @ X24)
% 0.19/0.55          | ~ (l1_pre_topc @ X26)
% 0.19/0.55          | (v2_struct_0 @ X26)
% 0.19/0.55          | ~ (l1_pre_topc @ X24))),
% 0.19/0.55      inference('cnf', [status(esa)], [t24_compts_1])).
% 0.19/0.55  thf('76', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | (v2_struct_0 @ sk_B)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.55          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.19/0.55          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.19/0.55          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55              != (k2_struct_0 @ sk_B))
% 0.19/0.55          | (v2_compts_1 @ 
% 0.19/0.55             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0) @ 
% 0.19/0.55             sk_B)
% 0.19/0.55          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.55  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('79', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('80', plain,
% 0.19/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.55         = (k2_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('81', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('83', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_B)
% 0.19/0.55          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.19/0.55          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.19/0.55          | (v2_compts_1 @ 
% 0.19/0.55             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0) @ 
% 0.19/0.55             sk_B)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)],
% 0.19/0.55                ['76', '77', '78', '79', '80', '81', '82'])).
% 0.19/0.55  thf('84', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | (v2_compts_1 @ 
% 0.19/0.55             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0) @ 
% 0.19/0.55             sk_B)
% 0.19/0.55          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.19/0.55          | (v2_struct_0 @ sk_B))),
% 0.19/0.55      inference('simplify', [status(thm)], ['83'])).
% 0.19/0.55  thf('85', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | (v2_struct_0 @ sk_B)
% 0.19/0.55        | ~ (v2_compts_1 @ 
% 0.19/0.55             (sk_D @ 
% 0.19/0.55              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55              sk_A @ sk_B) @ 
% 0.19/0.55             sk_A)
% 0.19/0.55        | (v2_compts_1 @ 
% 0.19/0.55           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55            (sk_D @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_A @ sk_B)) @ 
% 0.19/0.55           sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['73', '84'])).
% 0.19/0.55  thf('86', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | (v2_compts_1 @ 
% 0.19/0.55           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55            (sk_D @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_A @ sk_B)) @ 
% 0.19/0.55           sk_B)
% 0.19/0.55        | (v2_struct_0 @ sk_B)
% 0.19/0.55        | (v5_pre_topc @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           sk_B @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['72', '85'])).
% 0.19/0.55  thf('87', plain,
% 0.19/0.55      (((v2_struct_0 @ sk_B)
% 0.19/0.55        | (v2_compts_1 @ 
% 0.19/0.55           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55            (sk_D @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_A @ sk_B)) @ 
% 0.19/0.55           sk_B)
% 0.19/0.55        | (v5_pre_topc @ 
% 0.19/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55           sk_B @ sk_A))),
% 0.19/0.55      inference('simplify', [status(thm)], ['86'])).
% 0.19/0.55  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('89', plain,
% 0.19/0.55      (((v5_pre_topc @ 
% 0.19/0.55         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55         sk_B @ sk_A)
% 0.19/0.55        | (v2_compts_1 @ 
% 0.19/0.55           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55            (sk_D @ 
% 0.19/0.55             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55             sk_A @ sk_B)) @ 
% 0.19/0.55           sk_B))),
% 0.19/0.55      inference('clc', [status(thm)], ['87', '88'])).
% 0.19/0.55  thf('90', plain,
% 0.19/0.55      (~ (v5_pre_topc @ 
% 0.19/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55          sk_B @ sk_A)),
% 0.19/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.19/0.55  thf('91', plain,
% 0.19/0.55      ((v2_compts_1 @ 
% 0.19/0.55        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55         (sk_D @ 
% 0.19/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55          sk_A @ sk_B)) @ 
% 0.19/0.55        sk_B)),
% 0.19/0.55      inference('clc', [status(thm)], ['89', '90'])).
% 0.19/0.55  thf('92', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(dt_k7_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.55  thf('93', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.19/0.55          | (m1_subset_1 @ (k7_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.19/0.55             (k1_zfmisc_1 @ X2)))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.19/0.55  thf('94', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (m1_subset_1 @ 
% 0.19/0.55          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55           X0) @ 
% 0.19/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.19/0.55  thf(t16_compts_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.19/0.55             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.19/0.55  thf('95', plain,
% 0.19/0.55      (![X19 : $i, X20 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.55          | (v4_pre_topc @ X19 @ X20)
% 0.19/0.55          | ~ (v2_compts_1 @ X19 @ X20)
% 0.19/0.55          | ~ (v8_pre_topc @ X20)
% 0.19/0.55          | ~ (l1_pre_topc @ X20)
% 0.19/0.55          | ~ (v2_pre_topc @ X20))),
% 0.19/0.55      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.19/0.55  thf('96', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (v2_pre_topc @ sk_B)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.55          | ~ (v8_pre_topc @ sk_B)
% 0.19/0.55          | ~ (v2_compts_1 @ 
% 0.19/0.55               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55                sk_C @ X0) @ 
% 0.19/0.55               sk_B)
% 0.19/0.55          | (v4_pre_topc @ 
% 0.19/0.55             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0) @ 
% 0.19/0.55             sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.55  thf('97', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('99', plain, ((v8_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('100', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (v2_compts_1 @ 
% 0.19/0.55             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0) @ 
% 0.19/0.55             sk_B)
% 0.19/0.55          | (v4_pre_topc @ 
% 0.19/0.55             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.55              sk_C @ X0) @ 
% 0.19/0.55             sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 0.19/0.55  thf('101', plain,
% 0.19/0.55      ((v4_pre_topc @ 
% 0.19/0.55        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.55         (sk_D @ 
% 0.19/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55          sk_A @ sk_B)) @ 
% 0.19/0.55        sk_B)),
% 0.19/0.55      inference('sup-', [status(thm)], ['91', '100'])).
% 0.19/0.55  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('103', plain,
% 0.19/0.55      ((v1_funct_1 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.55  thf('104', plain,
% 0.19/0.55      ((v1_funct_2 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.19/0.55  thf('105', plain,
% 0.19/0.55      ((m1_subset_1 @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.55  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('107', plain,
% 0.19/0.55      ((v5_pre_topc @ 
% 0.19/0.55        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.55        sk_B @ sk_A)),
% 0.19/0.55      inference('demod', [status(thm)],
% 0.19/0.55                ['57', '101', '102', '103', '104', '105', '106'])).
% 0.19/0.55  thf('108', plain, ($false), inference('demod', [status(thm)], ['14', '107'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
