%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btO47xk7h1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:32 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 545 expanded)
%              Number of leaves         :   35 ( 183 expanded)
%              Depth                    :   15
%              Number of atoms          : 2394 (15865 expanded)
%              Number of equality atoms :   42 (  58 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_connsp_1_type,type,(
    v2_connsp_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v2_connsp_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) @ X27 @ X25 ) @ X24 )
      | ~ ( v2_connsp_1 @ X25 @ X26 )
      | ~ ( v5_pre_topc @ X27 @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tops_2 @ X6 @ X7 @ X5 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 ) @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

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

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ X21 )
        = ( k8_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 ) @ X21 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 )
       != ( k2_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t67_tops_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('51',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X11 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 )
       != ( k2_struct_0 @ X11 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 ) )
        = ( k2_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('54',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tops_2 @ X6 @ X7 @ X5 )
      | ( v2_funct_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63','64','65','66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tops_2 @ X6 @ X7 @ X5 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 )
        = ( k2_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('79',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','57','58','59','68','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) @ X16 )
       != ( k2_struct_0 @ X14 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('85',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63','64','65','66','67'])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('92',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91'])).

thf('93',plain,(
    v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf('95',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X17 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 )
       != ( k2_struct_0 @ X17 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 ) ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_tops_2])).

thf('96',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63','64','65','66','67'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('103',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98','99','100','101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('108',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('111',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('112',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

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

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('116',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('119',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('120',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('122',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('123',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('125',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('126',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','120','126'])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['106','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['46','49','50','51','82','93','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ X0 )
        = ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D )
    = ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['43','135'])).

thf('137',plain,(
    v2_connsp_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['42','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['0','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btO47xk7h1
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 192 iterations in 0.203s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.67  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.67  thf(v2_connsp_1_type, type, v2_connsp_1: $i > $i > $o).
% 0.45/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.45/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.67  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.45/0.67  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.67  thf(t76_tops_2, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.67             ( l1_pre_topc @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ![D:$i]:
% 0.45/0.67                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.67                   ( ( ( v3_tops_2 @ C @ A @ B ) & ( v2_connsp_1 @ D @ B ) ) =>
% 0.45/0.67                     ( v2_connsp_1 @
% 0.45/0.67                       ( k8_relset_1 @
% 0.45/0.67                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.45/0.67                       A ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67            ( l1_pre_topc @ A ) ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.67                ( l1_pre_topc @ B ) ) =>
% 0.45/0.67              ( ![C:$i]:
% 0.45/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                    ( v1_funct_2 @
% 0.45/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                    ( m1_subset_1 @
% 0.45/0.67                      C @ 
% 0.45/0.67                      ( k1_zfmisc_1 @
% 0.45/0.67                        ( k2_zfmisc_1 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67                  ( ![D:$i]:
% 0.45/0.67                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.45/0.67                      ( ( ( v3_tops_2 @ C @ A @ B ) & ( v2_connsp_1 @ D @ B ) ) =>
% 0.45/0.67                        ( v2_connsp_1 @
% 0.45/0.67                          ( k8_relset_1 @
% 0.45/0.67                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.45/0.67                          A ) ) ) ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t76_tops_2])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (~ (v2_connsp_1 @ 
% 0.45/0.67          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.67           sk_D) @ 
% 0.45/0.67          sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(dt_k2_tops_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.45/0.67         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.45/0.67         ( m1_subset_1 @
% 0.45/0.67           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.45/0.67           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         ((m1_subset_1 @ (k2_tops_2 @ X8 @ X9 @ X10) @ 
% 0.45/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.45/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.45/0.67          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.45/0.67          | ~ (v1_funct_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (m1_subset_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.67  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      ((m1_subset_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.67  thf(t75_tops_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.45/0.67             ( l1_pre_topc @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ![D:$i]:
% 0.45/0.67                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67                   ( ( ( v5_pre_topc @ C @ A @ B ) & ( v2_connsp_1 @ D @ A ) ) =>
% 0.45/0.67                     ( v2_connsp_1 @
% 0.45/0.67                       ( k7_relset_1 @
% 0.45/0.67                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.45/0.67                       B ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X24)
% 0.45/0.67          | ~ (v2_pre_topc @ X24)
% 0.45/0.67          | ~ (l1_pre_topc @ X24)
% 0.45/0.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.67          | (v2_connsp_1 @ 
% 0.45/0.67             (k7_relset_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24) @ X27 @ 
% 0.45/0.67              X25) @ 
% 0.45/0.67             X24)
% 0.45/0.67          | ~ (v2_connsp_1 @ X25 @ X26)
% 0.45/0.67          | ~ (v5_pre_topc @ X27 @ X26 @ X24)
% 0.45/0.67          | ~ (m1_subset_1 @ X27 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))))
% 0.45/0.67          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X24))
% 0.45/0.67          | ~ (v1_funct_1 @ X27)
% 0.45/0.67          | ~ (l1_pre_topc @ X26)
% 0.45/0.67          | ~ (v2_pre_topc @ X26)
% 0.45/0.67          | (v2_struct_0 @ X26))),
% 0.45/0.67      inference('cnf', [status(esa)], [t75_tops_2])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.45/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.45/0.67          | ~ (v1_funct_1 @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67          | ~ (v1_funct_2 @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.67          | ~ (v5_pre_topc @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67               sk_B @ sk_A)
% 0.45/0.67          | ~ (v2_connsp_1 @ X0 @ sk_B)
% 0.45/0.67          | (v2_connsp_1 @ 
% 0.45/0.67             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67              X0) @ 
% 0.45/0.67             sk_A)
% 0.45/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.45/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.67  thf('10', plain, ((v2_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         ((v1_funct_1 @ (k2_tops_2 @ X8 @ X9 @ X10))
% 0.45/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.45/0.67          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.45/0.67          | ~ (v1_funct_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (v1_funct_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      ((v1_funct_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         ((v1_funct_2 @ (k2_tops_2 @ X8 @ X9 @ X10) @ X9 @ X8)
% 0.45/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.45/0.67          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.45/0.67          | ~ (v1_funct_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (v1_funct_2 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      ((v1_funct_2 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d5_tops_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_pre_topc @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( l1_pre_topc @ B ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.45/0.67                 ( ( ( k1_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                     ( k2_struct_0 @ A ) ) & 
% 0.45/0.67                   ( ( k2_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.45/0.67                   ( v5_pre_topc @
% 0.45/0.67                     ( k2_tops_2 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.45/0.67                     B @ A ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X5)
% 0.45/0.67          | ~ (v3_tops_2 @ X6 @ X7 @ X5)
% 0.45/0.67          | (v5_pre_topc @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6) @ X5 @ 
% 0.45/0.67             X7)
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.45/0.67          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.45/0.67          | ~ (v1_funct_1 @ X6)
% 0.45/0.67          | ~ (l1_pre_topc @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (v5_pre_topc @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67           sk_B @ sk_A)
% 0.45/0.67        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('30', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      ((v5_pre_topc @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        sk_B @ sk_A)),
% 0.45/0.67      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.45/0.67  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_struct_0 @ sk_B)
% 0.45/0.67          | ~ (v2_connsp_1 @ X0 @ sk_B)
% 0.45/0.67          | (v2_connsp_1 @ 
% 0.45/0.67             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67              X0) @ 
% 0.45/0.67             sk_A)
% 0.45/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.45/0.67          | (v2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['9', '10', '11', '17', '23', '32', '33', '34'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A)
% 0.45/0.67        | (v2_connsp_1 @ 
% 0.45/0.67           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67            sk_D) @ 
% 0.45/0.67           sk_A)
% 0.45/0.67        | ~ (v2_connsp_1 @ sk_D @ sk_B)
% 0.45/0.67        | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '35'])).
% 0.45/0.67  thf('37', plain, ((v2_connsp_1 @ sk_D @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A)
% 0.45/0.67        | (v2_connsp_1 @ 
% 0.45/0.67           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67            sk_D) @ 
% 0.45/0.67           sk_A)
% 0.45/0.67        | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.67  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_B)
% 0.45/0.67        | (v2_connsp_1 @ 
% 0.45/0.67           (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67            sk_D) @ 
% 0.45/0.67           sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['38', '39'])).
% 0.45/0.67  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      ((v2_connsp_1 @ 
% 0.45/0.67        (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67         sk_D) @ 
% 0.45/0.67        sk_A)),
% 0.45/0.67      inference('clc', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      ((m1_subset_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.67  thf(t67_tops_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( l1_struct_0 @ B ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ![D:$i]:
% 0.45/0.67                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67                   ( ( ( ( k2_relset_1 @
% 0.45/0.67                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                         ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                       ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                     ( ( k7_relset_1 @
% 0.45/0.67                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.45/0.67                       ( k8_relset_1 @
% 0.45/0.67                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                         ( k2_tops_2 @
% 0.45/0.67                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.45/0.67                         D ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.67         (~ (l1_struct_0 @ X20)
% 0.45/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.45/0.67          | ((k7_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23 @ 
% 0.45/0.67              X21)
% 0.45/0.67              = (k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22) @ 
% 0.45/0.67                 (k2_tops_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23) @ 
% 0.45/0.67                 X21))
% 0.45/0.67          | ~ (v2_funct_1 @ X23)
% 0.45/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ X23)
% 0.45/0.67              != (k2_struct_0 @ X20))
% 0.45/0.67          | ~ (m1_subset_1 @ X23 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.45/0.67          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.45/0.67          | ~ (v1_funct_1 @ X23)
% 0.45/0.67          | ~ (l1_struct_0 @ X22))),
% 0.45/0.67      inference('cnf', [status(esa)], [t67_tops_2])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (l1_struct_0 @ sk_B)
% 0.45/0.67          | ~ (v1_funct_1 @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67          | ~ (v1_funct_2 @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.67          | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67              != (k2_struct_0 @ sk_A))
% 0.45/0.67          | ~ (v2_funct_1 @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67          | ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67              X0)
% 0.45/0.67              = (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67                 (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                  (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67                   sk_C)) @ 
% 0.45/0.67                 X0))
% 0.45/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.45/0.67          | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.67  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(dt_l1_pre_topc, axiom,
% 0.45/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.67  thf('48', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.67  thf('49', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      ((v1_funct_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      ((v1_funct_2 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t62_tops_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ( ( ( k2_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                 ( ( ( k1_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                       ( k2_tops_2 @
% 0.45/0.67                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.45/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                   ( ( k2_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                       ( k2_tops_2 @
% 0.45/0.67                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.45/0.67                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X11)
% 0.45/0.67          | ~ (l1_struct_0 @ X11)
% 0.45/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13)
% 0.45/0.67              != (k2_struct_0 @ X11))
% 0.45/0.67          | ~ (v2_funct_1 @ X13)
% 0.45/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13))
% 0.45/0.67              = (k2_struct_0 @ X12))
% 0.45/0.67          | ~ (m1_subset_1 @ X13 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))))
% 0.45/0.67          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 0.45/0.67          | ~ (v1_funct_1 @ X13)
% 0.45/0.67          | ~ (l1_struct_0 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      ((~ (l1_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67            = (k2_struct_0 @ sk_A))
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67            != (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.67        | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.67  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('56', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.67  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X5)
% 0.45/0.67          | ~ (v3_tops_2 @ X6 @ X7 @ X5)
% 0.45/0.67          | (v2_funct_1 @ X6)
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.45/0.67          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.45/0.67          | ~ (v1_funct_1 @ X6)
% 0.45/0.67          | ~ (l1_pre_topc @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (v2_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.67  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('66', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 0.45/0.67  thf('69', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('70', plain,
% 0.45/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X5)
% 0.45/0.67          | ~ (v3_tops_2 @ X6 @ X7 @ X5)
% 0.45/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6)
% 0.45/0.67              = (k2_struct_0 @ X5))
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.45/0.67          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.45/0.67          | ~ (v1_funct_1 @ X6)
% 0.45/0.67          | ~ (l1_pre_topc @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.45/0.67  thf('71', plain,
% 0.45/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67            = (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.67  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('74', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('75', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('76', plain, ((l1_pre_topc @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('77', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['71', '72', '73', '74', '75', '76'])).
% 0.45/0.67  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.67  thf('79', plain,
% 0.45/0.67      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67          = (k2_struct_0 @ sk_A))
% 0.45/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.67        | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['54', '57', '58', '59', '68', '77', '78'])).
% 0.45/0.67  thf('80', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_B)
% 0.45/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67            = (k2_struct_0 @ sk_A)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['79'])).
% 0.45/0.67  thf('81', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('82', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67         = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['80', '81'])).
% 0.45/0.67  thf('83', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t63_tops_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( l1_struct_0 @ B ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ( ( ( k2_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                 ( v2_funct_1 @
% 0.45/0.67                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('84', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.67         (~ (l1_struct_0 @ X14)
% 0.45/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14) @ X16)
% 0.45/0.67              != (k2_struct_0 @ X14))
% 0.45/0.67          | ~ (v2_funct_1 @ X16)
% 0.45/0.67          | (v2_funct_1 @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14) @ X16))
% 0.45/0.67          | ~ (m1_subset_1 @ X16 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.45/0.67          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.45/0.67          | ~ (v1_funct_1 @ X16)
% 0.45/0.67          | ~ (l1_struct_0 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.45/0.67  thf('85', plain,
% 0.45/0.67      ((~ (l1_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (v2_funct_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67            != (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.67  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('88', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 0.45/0.67  thf('90', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['71', '72', '73', '74', '75', '76'])).
% 0.45/0.67  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.67  thf('92', plain,
% 0.45/0.67      (((v2_funct_1 @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['85', '86', '87', '88', '89', '90', '91'])).
% 0.45/0.67  thf('93', plain,
% 0.45/0.67      ((v2_funct_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.45/0.67      inference('simplify', [status(thm)], ['92'])).
% 0.45/0.67  thf('94', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t64_tops_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ( ( ( k2_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                 ( r2_funct_2 @
% 0.45/0.67                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.67                   ( k2_tops_2 @
% 0.45/0.67                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                     ( k2_tops_2 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.67                   C ) ) ) ) ) ) ))).
% 0.45/0.67  thf('95', plain,
% 0.45/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X17)
% 0.45/0.67          | ~ (l1_struct_0 @ X17)
% 0.45/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19)
% 0.45/0.67              != (k2_struct_0 @ X17))
% 0.45/0.67          | ~ (v2_funct_1 @ X19)
% 0.45/0.67          | (r2_funct_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19)) @ 
% 0.45/0.67             X19)
% 0.45/0.67          | ~ (m1_subset_1 @ X19 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 0.45/0.67          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.45/0.67          | ~ (v1_funct_1 @ X19)
% 0.45/0.67          | ~ (l1_struct_0 @ X18))),
% 0.45/0.67      inference('cnf', [status(esa)], [t64_tops_2])).
% 0.45/0.67  thf('96', plain,
% 0.45/0.67      ((~ (l1_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           sk_C)
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.67        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67            != (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.67        | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.67  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('99', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 0.45/0.67  thf('101', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['71', '72', '73', '74', '75', '76'])).
% 0.45/0.67  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.67  thf('103', plain,
% 0.45/0.67      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67         sk_C)
% 0.45/0.67        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.45/0.67        | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['96', '97', '98', '99', '100', '101', '102'])).
% 0.45/0.67  thf('104', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_B)
% 0.45/0.67        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           sk_C))),
% 0.45/0.67      inference('simplify', [status(thm)], ['103'])).
% 0.45/0.67  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('106', plain,
% 0.45/0.67      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67        sk_C)),
% 0.45/0.67      inference('clc', [status(thm)], ['104', '105'])).
% 0.45/0.67  thf('107', plain,
% 0.45/0.67      ((m1_subset_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.67  thf('108', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         ((m1_subset_1 @ (k2_tops_2 @ X8 @ X9 @ X10) @ 
% 0.45/0.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.45/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.45/0.67          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.45/0.67          | ~ (v1_funct_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.67  thf('109', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67        | ~ (v1_funct_2 @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.67        | (m1_subset_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['107', '108'])).
% 0.45/0.67  thf('110', plain,
% 0.45/0.67      ((v1_funct_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.45/0.67  thf('111', plain,
% 0.45/0.67      ((v1_funct_2 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.45/0.67  thf('112', plain,
% 0.45/0.67      ((m1_subset_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.45/0.67  thf(redefinition_r2_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.67         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.67  thf('113', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.45/0.67          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.45/0.67          | ~ (v1_funct_1 @ X0)
% 0.45/0.67          | ~ (v1_funct_1 @ X3)
% 0.45/0.67          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.45/0.67          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.45/0.67          | ((X0) = (X3))
% 0.45/0.67          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.45/0.67  thf('114', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67             X0)
% 0.45/0.67          | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67              = (X0))
% 0.45/0.67          | ~ (m1_subset_1 @ X0 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (v1_funct_1 @ X0)
% 0.45/0.67          | ~ (v1_funct_1 @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.45/0.67          | ~ (v1_funct_2 @ 
% 0.45/0.67               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['112', '113'])).
% 0.45/0.67  thf('115', plain,
% 0.45/0.67      ((m1_subset_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.67  thf('116', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         ((v1_funct_1 @ (k2_tops_2 @ X8 @ X9 @ X10))
% 0.45/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.45/0.67          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.45/0.67          | ~ (v1_funct_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.67  thf('117', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67        | ~ (v1_funct_2 @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.67        | (v1_funct_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['115', '116'])).
% 0.45/0.67  thf('118', plain,
% 0.45/0.67      ((v1_funct_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.45/0.67  thf('119', plain,
% 0.45/0.67      ((v1_funct_2 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.45/0.67  thf('120', plain,
% 0.45/0.67      ((v1_funct_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.45/0.67  thf('121', plain,
% 0.45/0.67      ((m1_subset_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.67  thf('122', plain,
% 0.45/0.67      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.67         ((v1_funct_2 @ (k2_tops_2 @ X8 @ X9 @ X10) @ X9 @ X8)
% 0.45/0.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.45/0.67          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.45/0.67          | ~ (v1_funct_1 @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.67  thf('123', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67        | ~ (v1_funct_2 @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.45/0.67        | (v1_funct_2 @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['121', '122'])).
% 0.45/0.67  thf('124', plain,
% 0.45/0.67      ((v1_funct_1 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.45/0.67  thf('125', plain,
% 0.45/0.67      ((v1_funct_2 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.45/0.67  thf('126', plain,
% 0.45/0.67      ((v1_funct_2 @ 
% 0.45/0.67        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.45/0.67  thf('127', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67             X0)
% 0.45/0.67          | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67              = (X0))
% 0.45/0.67          | ~ (m1_subset_1 @ X0 @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67          | ~ (v1_funct_1 @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['114', '120', '126'])).
% 0.45/0.67  thf('128', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ~ (m1_subset_1 @ sk_C @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67            = (sk_C)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['106', '127'])).
% 0.45/0.67  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('130', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('131', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('132', plain,
% 0.45/0.67      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.67         = (sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.45/0.67  thf('133', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.67  thf('134', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.45/0.67          | ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67              X0)
% 0.45/0.67              = (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67                 sk_C @ X0))
% 0.45/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)],
% 0.45/0.67                ['46', '49', '50', '51', '82', '93', '132', '133'])).
% 0.45/0.67  thf('135', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.45/0.67          | ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67              X0)
% 0.45/0.67              = (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67                 sk_C @ X0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['134'])).
% 0.45/0.67  thf('136', plain,
% 0.45/0.67      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.67         sk_D)
% 0.45/0.67         = (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.67            sk_D))),
% 0.45/0.67      inference('sup-', [status(thm)], ['43', '135'])).
% 0.45/0.67  thf('137', plain,
% 0.45/0.67      ((v2_connsp_1 @ 
% 0.45/0.67        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.67         sk_D) @ 
% 0.45/0.67        sk_A)),
% 0.45/0.67      inference('demod', [status(thm)], ['42', '136'])).
% 0.45/0.67  thf('138', plain, ($false), inference('demod', [status(thm)], ['0', '137'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.53/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
