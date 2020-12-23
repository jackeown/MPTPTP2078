%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YAQbMjseTb

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:29 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  306 (5597 expanded)
%              Number of leaves         :   33 (1697 expanded)
%              Depth                    :   29
%              Number of atoms          : 3488 (121407 expanded)
%              Number of equality atoms :  132 (1789 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t70_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
               => ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_tops_2 @ C @ A @ B )
                 => ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_tops_2])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X10 @ X12 )
       != X10 )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k2_tops_2 @ X11 @ X10 @ X12 )
        = ( k2_funct_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X14 )
        = ( k2_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','21'])).

thf('23',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
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
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('33',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X14 )
       != ( k2_struct_0 @ X15 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X14 )
       != ( k2_struct_0 @ X13 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v5_pre_topc @ X14 @ X15 @ X13 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X14 ) @ X13 @ X15 )
      | ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('51',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X14 ) @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
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

thf('58',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('59',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['54','55','56','57','58','59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','51','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('70',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('73',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X10 @ X12 )
       != X10 )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k2_tops_2 @ X11 @ X10 @ X12 )
        = ( k2_funct_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','94'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','95'])).

thf('97',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('99',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('101',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('103',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('104',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('105',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('107',plain,(
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

thf('108',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 )
       != ( k2_struct_0 @ X19 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 ) )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('109',plain,
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
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','21'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('117',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110','111','112','113','114','115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','101','102','103','104','105','106','120'])).

thf('122',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['72','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('124',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('128',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['122','125','126','127'])).

thf('129',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['71','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,(
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

thf('135',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X22 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) @ X24 )
       != ( k2_struct_0 @ X22 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) @ X24 ) ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_tops_2])).

thf('136',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('142',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','21'])).

thf('143',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('144',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','141','142','143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['133','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('150',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('153',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('154',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('157',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X10 @ X12 )
       != X10 )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k2_tops_2 @ X11 @ X10 @ X12 )
        = ( k2_funct_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('159',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','94'])).

thf('161',plain,
    ( ~ ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('164',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('165',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('168',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('169',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('171',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('172',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('173',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('174',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('175',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('176',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('178',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','162','169','170','171','172','173','178'])).

thf('180',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['151','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['123','124'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('185',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('186',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['150','185'])).

thf('187',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('188',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('189',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('190',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('192',plain,
    ( ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('194',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('195',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('196',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['187','196'])).

thf('198',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('199',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('201',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['199','200'])).

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

thf('202',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X5 @ X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( X4 = X7 )
      | ~ ( r2_funct_2 @ X5 @ X6 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('205',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','39'])).

thf('206',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('207',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('209',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('211',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['204','211'])).

thf('213',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('214',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('216',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('218',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','39'])).

thf('219',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X16 @ X17 @ X18 ) @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('220',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('222',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('224',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['217','224'])).

thf('226',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('227',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('229',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['203','216','229'])).

thf('231',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['186','230'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['132','235'])).

thf('237',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ( v5_pre_topc @ X14 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('239',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['239','240','241','242','243','244'])).

thf('246',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('247',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 )
       != ( k2_struct_0 @ X19 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 ) )
        = ( k2_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('249',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('251',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('254',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('255',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','21'])).

thf('256',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('257',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['249','250','251','252','253','254','255','256'])).

thf('258',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','70','236','245','246','260'])).

thf('262',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('265',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['262','265'])).

thf('267',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','266'])).

thf('268',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['123','124'])).

thf('269',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('271',plain,(
    $false ),
    inference(demod,[status(thm)],['267','268','269','270'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YAQbMjseTb
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:25:54 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 1229 iterations in 0.295s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.55/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.74  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.55/0.74  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.55/0.74  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.74  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.55/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(fc6_funct_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.55/0.74       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.74         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.74         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.74          | ~ (v2_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_funct_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X0))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.74  thf(t70_tops_2, conjecture,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                 ( m1_subset_1 @
% 0.55/0.74                   C @ 
% 0.55/0.74                   ( k1_zfmisc_1 @
% 0.55/0.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.55/0.74                 ( v3_tops_2 @
% 0.55/0.74                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.55/0.74                   B @ A ) ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i]:
% 0.55/0.74        ( ( l1_pre_topc @ A ) =>
% 0.55/0.74          ( ![B:$i]:
% 0.55/0.74            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.55/0.74              ( ![C:$i]:
% 0.55/0.74                ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.74                    ( v1_funct_2 @
% 0.55/0.74                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                    ( m1_subset_1 @
% 0.55/0.74                      C @ 
% 0.55/0.74                      ( k1_zfmisc_1 @
% 0.55/0.74                        ( k2_zfmisc_1 @
% 0.55/0.74                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.55/0.74                    ( v3_tops_2 @
% 0.55/0.74                      ( k2_tops_2 @
% 0.55/0.74                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.55/0.74                      B @ A ) ) ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_k2_tops_2, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.74       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.55/0.74         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.55/0.74         ( m1_subset_1 @
% 0.55/0.74           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.55/0.74           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (k2_tops_2 @ X16 @ X17 @ X18) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.74          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.74          | ~ (v1_funct_1 @ X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | (m1_subset_1 @ 
% 0.55/0.74           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.74           (k1_zfmisc_1 @ 
% 0.55/0.74            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      ((m1_subset_1 @ 
% 0.55/0.74        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.55/0.74  thf(d3_struct_0, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X8 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d4_tops_2, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.74       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.55/0.74         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.55/0.74         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.55/0.74          | ~ (v2_funct_1 @ X12)
% 0.55/0.74          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.55/0.74          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.55/0.74          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.55/0.74          | ~ (v1_funct_1 @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            = (k2_funct_1 @ sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            != (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74          = (k2_funct_1 @ sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            != (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d5_tops_2, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( l1_pre_topc @ B ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                 ( m1_subset_1 @
% 0.55/0.74                   C @ 
% 0.55/0.74                   ( k1_zfmisc_1 @
% 0.55/0.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.55/0.74                 ( ( ( k1_relset_1 @
% 0.55/0.74                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.74                     ( k2_struct_0 @ A ) ) & 
% 0.55/0.74                   ( ( k2_relset_1 @
% 0.55/0.74                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.74                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.74                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.55/0.74                   ( v5_pre_topc @
% 0.55/0.74                     ( k2_tops_2 @
% 0.55/0.74                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.55/0.74                     B @ A ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X13)
% 0.55/0.74          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.55/0.74          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14)
% 0.55/0.74              = (k2_struct_0 @ X13))
% 0.55/0.74          | ~ (m1_subset_1 @ X14 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.55/0.74          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.55/0.74          | ~ (v1_funct_1 @ X14)
% 0.55/0.74          | ~ (l1_pre_topc @ X15))),
% 0.55/0.74      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            = (k2_struct_0 @ sk_B))
% 0.55/0.74        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.55/0.74  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('20', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74         = (k2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['16', '17', '18', '19', '20', '21'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74          = (k2_funct_1 @ sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.74        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['13', '22'])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X13)
% 0.55/0.74          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.55/0.74          | (v2_funct_1 @ X14)
% 0.55/0.74          | ~ (m1_subset_1 @ X14 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.55/0.74          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.55/0.74          | ~ (v1_funct_1 @ X14)
% 0.55/0.74          | ~ (l1_pre_topc @ X15))),
% 0.55/0.74      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | (v2_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.74  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('30', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('32', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74          = (k2_funct_1 @ sk_C))
% 0.55/0.74        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['23', '32'])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.55/0.74        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.74        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            = (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['7', '33'])).
% 0.55/0.74  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_l1_pre_topc, axiom,
% 0.55/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.55/0.74  thf('36', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.74  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.74      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.55/0.74        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74            = (k2_funct_1 @ sk_C)))),
% 0.55/0.74      inference('demod', [status(thm)], ['34', '37'])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.74         = (k2_funct_1 @ sk_C))),
% 0.55/0.74      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['6', '39'])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X13)
% 0.55/0.74          | ((k1_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14)
% 0.55/0.74              != (k2_struct_0 @ X15))
% 0.55/0.74          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14)
% 0.55/0.74              != (k2_struct_0 @ X13))
% 0.55/0.74          | ~ (v2_funct_1 @ X14)
% 0.55/0.74          | ~ (v5_pre_topc @ X14 @ X15 @ X13)
% 0.55/0.74          | ~ (v5_pre_topc @ 
% 0.55/0.74               (k2_tops_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14) @ 
% 0.55/0.74               X13 @ X15)
% 0.55/0.74          | (v3_tops_2 @ X14 @ X15 @ X13)
% 0.55/0.74          | ~ (m1_subset_1 @ X14 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.55/0.74          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.55/0.74          | ~ (v1_funct_1 @ X14)
% 0.55/0.74          | ~ (l1_pre_topc @ X15))),
% 0.55/0.74      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.74             (u1_struct_0 @ sk_A))
% 0.55/0.74        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.55/0.74        | ~ (v5_pre_topc @ 
% 0.55/0.74             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74              (k2_funct_1 @ sk_C)) @ 
% 0.55/0.74             sk_A @ sk_B)
% 0.55/0.74        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.55/0.74        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.55/0.74        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.74            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.55/0.74  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.74         ((v1_funct_1 @ (k2_tops_2 @ X16 @ X17 @ X18))
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.74          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.74          | ~ (v1_funct_1 @ X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.74        | (v1_funct_1 @ 
% 0.55/0.74           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.55/0.74  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('49', plain,
% 0.55/0.75      ((v1_funct_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.55/0.75  thf('50', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('51', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf('52', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('53', plain,
% 0.55/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X13)
% 0.55/0.75          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.55/0.75          | (v5_pre_topc @ 
% 0.55/0.75             (k2_tops_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14) @ 
% 0.55/0.75             X13 @ X15)
% 0.55/0.75          | ~ (m1_subset_1 @ X14 @ 
% 0.55/0.75               (k1_zfmisc_1 @ 
% 0.55/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.55/0.75          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.55/0.75          | ~ (v1_funct_1 @ X14)
% 0.55/0.75          | ~ (l1_pre_topc @ X15))),
% 0.55/0.75      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.55/0.75  thf('54', plain,
% 0.55/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | (v5_pre_topc @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75           sk_B @ sk_A)
% 0.55/0.75        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.55/0.75        | ~ (l1_pre_topc @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.75  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('57', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('58', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('59', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('61', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['54', '55', '56', '57', '58', '59', '60'])).
% 0.55/0.75  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('63', plain,
% 0.55/0.75      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75           (u1_struct_0 @ sk_A))
% 0.55/0.75        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.55/0.75        | ~ (v5_pre_topc @ 
% 0.55/0.75             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75              (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75             sk_A @ sk_B)
% 0.55/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.55/0.75        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)], ['42', '43', '51', '61', '62'])).
% 0.55/0.75  thf('64', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('65', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         ((v1_funct_2 @ (k2_tops_2 @ X16 @ X17 @ X18) @ X17 @ X16)
% 0.55/0.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.75          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.75          | ~ (v1_funct_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.75  thf('66', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | (v1_funct_2 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.75  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('68', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('69', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('70', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.55/0.75  thf('71', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('72', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.75  thf('73', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('74', plain,
% 0.55/0.75      ((m1_subset_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.55/0.75  thf('75', plain,
% 0.55/0.75      (((m1_subset_1 @ 
% 0.55/0.75         (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['73', '74'])).
% 0.55/0.75  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('77', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.75  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('79', plain,
% 0.55/0.75      ((m1_subset_1 @ 
% 0.55/0.75        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['75', '78'])).
% 0.55/0.75  thf('80', plain,
% 0.55/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.55/0.75         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.55/0.75          | ~ (v2_funct_1 @ X12)
% 0.55/0.75          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.55/0.75          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.55/0.75          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.55/0.75          | ~ (v1_funct_1 @ X12))),
% 0.55/0.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.75  thf('81', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75        | ~ (v1_funct_2 @ 
% 0.55/0.75             (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            = (k2_funct_1 @ 
% 0.55/0.75               (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.55/0.75        | ~ (v2_funct_1 @ 
% 0.55/0.75             (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            != (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['79', '80'])).
% 0.55/0.75  thf('82', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('83', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('84', plain,
% 0.55/0.75      (((m1_subset_1 @ sk_C @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['82', '83'])).
% 0.55/0.75  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('86', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['84', '85'])).
% 0.55/0.75  thf('87', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_tops_2 @ X16 @ X17 @ X18))
% 0.55/0.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.75          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.75          | ~ (v1_funct_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.75  thf('88', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | (v1_funct_1 @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['86', '87'])).
% 0.55/0.75  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('90', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('91', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('92', plain,
% 0.55/0.75      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['90', '91'])).
% 0.55/0.75  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('94', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['92', '93'])).
% 0.55/0.75  thf('95', plain,
% 0.55/0.75      ((v1_funct_1 @ 
% 0.55/0.75        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['88', '89', '94'])).
% 0.55/0.75  thf('96', plain,
% 0.55/0.75      ((~ (v1_funct_2 @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            = (k2_funct_1 @ 
% 0.55/0.75               (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.55/0.75        | ~ (v2_funct_1 @ 
% 0.55/0.75             (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            != (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['81', '95'])).
% 0.55/0.75  thf('97', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('98', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('99', plain,
% 0.55/0.75      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75          = (k2_funct_1 @ sk_C))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['97', '98'])).
% 0.55/0.75  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('101', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('102', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.55/0.75  thf('103', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('104', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('105', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('106', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('107', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(t62_tops_2, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( l1_struct_0 @ A ) =>
% 0.55/0.75       ( ![B:$i]:
% 0.55/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.75           ( ![C:$i]:
% 0.55/0.75             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.75                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.75                 ( m1_subset_1 @
% 0.55/0.75                   C @ 
% 0.55/0.75                   ( k1_zfmisc_1 @
% 0.55/0.75                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.75               ( ( ( ( k2_relset_1 @
% 0.55/0.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.75                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.75                   ( v2_funct_1 @ C ) ) =>
% 0.55/0.75                 ( ( ( k1_relset_1 @
% 0.55/0.75                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.75                       ( k2_tops_2 @
% 0.55/0.75                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.75                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.75                   ( ( k2_relset_1 @
% 0.55/0.75                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.75                       ( k2_tops_2 @
% 0.55/0.75                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.55/0.75                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.55/0.75  thf('108', plain,
% 0.55/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.75         ((v2_struct_0 @ X19)
% 0.55/0.75          | ~ (l1_struct_0 @ X19)
% 0.55/0.75          | ((k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21)
% 0.55/0.75              != (k2_struct_0 @ X19))
% 0.55/0.75          | ~ (v2_funct_1 @ X21)
% 0.55/0.75          | ((k2_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20) @ 
% 0.55/0.75              (k2_tops_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21))
% 0.55/0.75              = (k2_struct_0 @ X20))
% 0.55/0.75          | ~ (m1_subset_1 @ X21 @ 
% 0.55/0.75               (k1_zfmisc_1 @ 
% 0.55/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.55/0.75          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.55/0.75          | ~ (v1_funct_1 @ X21)
% 0.55/0.75          | ~ (l1_struct_0 @ X20))),
% 0.55/0.75      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.55/0.75  thf('109', plain,
% 0.55/0.75      ((~ (l1_struct_0 @ sk_A)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            = (k2_struct_0 @ sk_A))
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75            != (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.75        | (v2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['107', '108'])).
% 0.55/0.75  thf('110', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('112', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('113', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.55/0.75  thf('115', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['16', '17', '18', '19', '20', '21'])).
% 0.55/0.75  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.75  thf('117', plain,
% 0.55/0.75      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.55/0.75        | (v2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['109', '110', '111', '112', '113', '114', '115', '116'])).
% 0.55/0.75  thf('118', plain,
% 0.55/0.75      (((v2_struct_0 @ sk_B)
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['117'])).
% 0.55/0.75  thf('119', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('120', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('clc', [status(thm)], ['118', '119'])).
% 0.55/0.75  thf('121', plain,
% 0.55/0.75      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['96', '101', '102', '103', '104', '105', '106', '120'])).
% 0.55/0.75  thf('122', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['72', '121'])).
% 0.55/0.75  thf('123', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(cc1_relset_1, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i]:
% 0.55/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.75       ( v1_relat_1 @ C ) ))).
% 0.55/0.75  thf('124', plain,
% 0.55/0.75      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.75         ((v1_relat_1 @ X1)
% 0.55/0.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.55/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.55/0.75  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['123', '124'])).
% 0.55/0.75  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.55/0.75  thf('128', plain,
% 0.55/0.75      ((((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('demod', [status(thm)], ['122', '125', '126', '127'])).
% 0.55/0.75  thf('129', plain,
% 0.55/0.75      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A)
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['71', '128'])).
% 0.55/0.75  thf('130', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('131', plain,
% 0.55/0.75      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('demod', [status(thm)], ['129', '130'])).
% 0.55/0.75  thf('132', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['131'])).
% 0.55/0.75  thf('133', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('134', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf(t64_tops_2, axiom,
% 0.55/0.75    (![A:$i]:
% 0.55/0.75     ( ( l1_struct_0 @ A ) =>
% 0.55/0.75       ( ![B:$i]:
% 0.55/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.55/0.75           ( ![C:$i]:
% 0.55/0.75             ( ( ( v1_funct_1 @ C ) & 
% 0.55/0.75                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.75                 ( m1_subset_1 @
% 0.55/0.75                   C @ 
% 0.55/0.75                   ( k1_zfmisc_1 @
% 0.55/0.75                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.75               ( ( ( ( k2_relset_1 @
% 0.55/0.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.55/0.75                     ( k2_struct_0 @ B ) ) & 
% 0.55/0.75                   ( v2_funct_1 @ C ) ) =>
% 0.55/0.75                 ( r2_funct_2 @
% 0.55/0.75                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.55/0.75                   ( k2_tops_2 @
% 0.55/0.75                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.55/0.75                     ( k2_tops_2 @
% 0.55/0.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.55/0.75                   C ) ) ) ) ) ) ))).
% 0.55/0.75  thf('135', plain,
% 0.55/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.75         ((v2_struct_0 @ X22)
% 0.55/0.75          | ~ (l1_struct_0 @ X22)
% 0.55/0.75          | ((k2_relset_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22) @ X24)
% 0.55/0.75              != (k2_struct_0 @ X22))
% 0.55/0.75          | ~ (v2_funct_1 @ X24)
% 0.55/0.75          | (r2_funct_2 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22) @ 
% 0.55/0.75             (k2_tops_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23) @ 
% 0.55/0.75              (k2_tops_2 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22) @ X24)) @ 
% 0.55/0.75             X24)
% 0.55/0.75          | ~ (m1_subset_1 @ X24 @ 
% 0.55/0.75               (k1_zfmisc_1 @ 
% 0.55/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))))
% 0.55/0.75          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.55/0.75          | ~ (v1_funct_1 @ X24)
% 0.55/0.75          | ~ (l1_struct_0 @ X23))),
% 0.55/0.75      inference('cnf', [status(esa)], [t64_tops_2])).
% 0.55/0.75  thf('136', plain,
% 0.55/0.75      ((~ (l1_struct_0 @ sk_A)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.75           sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75            != (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.75        | (v2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['134', '135'])).
% 0.55/0.75  thf('137', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('139', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('140', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.55/0.75  thf('142', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['16', '17', '18', '19', '20', '21'])).
% 0.55/0.75  thf('143', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.75  thf('144', plain,
% 0.55/0.75      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75         sk_C)
% 0.55/0.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.55/0.75        | (v2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['136', '137', '138', '139', '140', '141', '142', '143'])).
% 0.55/0.75  thf('145', plain,
% 0.55/0.75      (((v2_struct_0 @ sk_B)
% 0.55/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75           sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['144'])).
% 0.55/0.75  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('147', plain,
% 0.55/0.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        sk_C)),
% 0.55/0.75      inference('clc', [status(thm)], ['145', '146'])).
% 0.55/0.75  thf('148', plain,
% 0.55/0.75      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75         sk_C)
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['133', '147'])).
% 0.55/0.75  thf('149', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('150', plain,
% 0.55/0.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['148', '149'])).
% 0.55/0.75  thf('151', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.55/0.75          | ~ (v2_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_relat_1 @ X0))),
% 0.55/0.75      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.55/0.75  thf('152', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['84', '85'])).
% 0.55/0.75  thf('153', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (k2_tops_2 @ X16 @ X17 @ X18) @ 
% 0.55/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.55/0.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.75          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.75          | ~ (v1_funct_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.75  thf('154', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | (m1_subset_1 @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['152', '153'])).
% 0.55/0.75  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('156', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['92', '93'])).
% 0.55/0.75  thf('157', plain,
% 0.55/0.75      ((m1_subset_1 @ 
% 0.55/0.75        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.55/0.75  thf('158', plain,
% 0.55/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.55/0.75         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.55/0.75          | ~ (v2_funct_1 @ X12)
% 0.55/0.75          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.55/0.75          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.55/0.75          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.55/0.75          | ~ (v1_funct_1 @ X12))),
% 0.55/0.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.55/0.75  thf('159', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75        | ~ (v1_funct_2 @ 
% 0.55/0.75             (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75             (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            = (k2_funct_1 @ 
% 0.55/0.75               (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.55/0.75        | ~ (v2_funct_1 @ 
% 0.55/0.75             (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            != (k2_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['157', '158'])).
% 0.55/0.75  thf('160', plain,
% 0.55/0.75      ((v1_funct_1 @ 
% 0.55/0.75        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['88', '89', '94'])).
% 0.55/0.75  thf('161', plain,
% 0.55/0.75      ((~ (v1_funct_2 @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75           (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            = (k2_funct_1 @ 
% 0.55/0.75               (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.55/0.75        | ~ (v2_funct_1 @ 
% 0.55/0.75             (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            != (k2_struct_0 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)], ['159', '160'])).
% 0.55/0.75  thf('162', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('163', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['84', '85'])).
% 0.55/0.75  thf('164', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         ((v1_funct_2 @ (k2_tops_2 @ X16 @ X17 @ X18) @ X17 @ X16)
% 0.55/0.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.75          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.75          | ~ (v1_funct_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.75  thf('165', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | (v1_funct_2 @ 
% 0.55/0.75           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75           (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['163', '164'])).
% 0.55/0.75  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('167', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['92', '93'])).
% 0.55/0.75  thf('168', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('169', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 0.55/0.75  thf('170', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('171', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('172', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('173', plain,
% 0.55/0.75      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.75  thf('174', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('175', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('clc', [status(thm)], ['118', '119'])).
% 0.55/0.75  thf('176', plain,
% 0.55/0.75      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['174', '175'])).
% 0.55/0.75  thf('177', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('178', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['176', '177'])).
% 0.55/0.75  thf('179', plain,
% 0.55/0.75      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['161', '162', '169', '170', '171', '172', '173', '178'])).
% 0.55/0.75  thf('180', plain,
% 0.55/0.75      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('simplify', [status(thm)], ['179'])).
% 0.55/0.75  thf('181', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['151', '180'])).
% 0.55/0.75  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['123', '124'])).
% 0.55/0.75  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.55/0.75  thf('185', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 0.55/0.75  thf('186', plain,
% 0.55/0.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['150', '185'])).
% 0.55/0.75  thf('187', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('188', plain,
% 0.55/0.75      ((m1_subset_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.55/0.75  thf('189', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         ((m1_subset_1 @ (k2_tops_2 @ X16 @ X17 @ X18) @ 
% 0.55/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.55/0.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.75          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.75          | ~ (v1_funct_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.75  thf('190', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75        | ~ (v1_funct_2 @ 
% 0.55/0.75             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.55/0.75        | (m1_subset_1 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['188', '189'])).
% 0.55/0.75  thf('191', plain,
% 0.55/0.75      ((v1_funct_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.55/0.75  thf('192', plain,
% 0.55/0.75      ((~ (v1_funct_2 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.55/0.75        | (m1_subset_1 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.55/0.75           (k1_zfmisc_1 @ 
% 0.55/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.55/0.75      inference('demod', [status(thm)], ['190', '191'])).
% 0.55/0.75  thf('193', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('194', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.55/0.75  thf('195', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('196', plain,
% 0.55/0.75      ((m1_subset_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 0.55/0.75  thf('197', plain,
% 0.55/0.75      (((m1_subset_1 @ 
% 0.55/0.75         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75         (k1_zfmisc_1 @ 
% 0.55/0.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['187', '196'])).
% 0.55/0.75  thf('198', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('199', plain,
% 0.55/0.75      ((m1_subset_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['197', '198'])).
% 0.55/0.75  thf('200', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 0.55/0.75  thf('201', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('demod', [status(thm)], ['199', '200'])).
% 0.55/0.75  thf(redefinition_r2_funct_2, axiom,
% 0.55/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.75         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.55/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.75       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.55/0.75  thf('202', plain,
% 0.55/0.75      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.55/0.75         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.55/0.75          | ~ (v1_funct_2 @ X4 @ X5 @ X6)
% 0.55/0.75          | ~ (v1_funct_1 @ X4)
% 0.55/0.75          | ~ (v1_funct_1 @ X7)
% 0.55/0.75          | ~ (v1_funct_2 @ X7 @ X5 @ X6)
% 0.55/0.75          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.55/0.75          | ((X4) = (X7))
% 0.55/0.75          | ~ (r2_funct_2 @ X5 @ X6 @ X4 @ X7))),
% 0.55/0.75      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.55/0.75  thf('203', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75             (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 0.55/0.75          | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (X0))
% 0.55/0.75          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.75               (k1_zfmisc_1 @ 
% 0.55/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.75          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75          | ~ (v1_funct_1 @ X0)
% 0.55/0.75          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.55/0.75          | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['201', '202'])).
% 0.55/0.75  thf('204', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('205', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['6', '39'])).
% 0.55/0.75  thf('206', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         ((v1_funct_1 @ (k2_tops_2 @ X16 @ X17 @ X18))
% 0.55/0.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.75          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.75          | ~ (v1_funct_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.75  thf('207', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75             (u1_struct_0 @ sk_A))
% 0.55/0.75        | (v1_funct_1 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('sup-', [status(thm)], ['205', '206'])).
% 0.55/0.75  thf('208', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf('209', plain,
% 0.55/0.75      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75           (u1_struct_0 @ sk_A))
% 0.55/0.75        | (v1_funct_1 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C))))),
% 0.55/0.75      inference('demod', [status(thm)], ['207', '208'])).
% 0.55/0.75  thf('210', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.55/0.75  thf('211', plain,
% 0.55/0.75      ((v1_funct_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['209', '210'])).
% 0.55/0.75  thf('212', plain,
% 0.55/0.75      (((v1_funct_1 @ 
% 0.55/0.75         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['204', '211'])).
% 0.55/0.75  thf('213', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('214', plain,
% 0.55/0.75      ((v1_funct_1 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['212', '213'])).
% 0.55/0.75  thf('215', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 0.55/0.75  thf('216', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['214', '215'])).
% 0.55/0.75  thf('217', plain,
% 0.55/0.75      (![X8 : $i]:
% 0.55/0.75         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.55/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.55/0.75  thf('218', plain,
% 0.55/0.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.75      inference('demod', [status(thm)], ['6', '39'])).
% 0.55/0.75  thf('219', plain,
% 0.55/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.75         ((v1_funct_2 @ (k2_tops_2 @ X16 @ X17 @ X18) @ X17 @ X16)
% 0.55/0.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.55/0.75          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.55/0.75          | ~ (v1_funct_1 @ X18))),
% 0.55/0.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.55/0.75  thf('220', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75             (u1_struct_0 @ sk_A))
% 0.55/0.75        | (v1_funct_2 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['218', '219'])).
% 0.55/0.75  thf('221', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.55/0.75  thf('222', plain,
% 0.55/0.75      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75           (u1_struct_0 @ sk_A))
% 0.55/0.75        | (v1_funct_2 @ 
% 0.55/0.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)], ['220', '221'])).
% 0.55/0.75  thf('223', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A))),
% 0.55/0.75      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.55/0.75  thf('224', plain,
% 0.55/0.75      ((v1_funct_2 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['222', '223'])).
% 0.55/0.75  thf('225', plain,
% 0.55/0.75      (((v1_funct_2 @ 
% 0.55/0.75         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.75      inference('sup+', [status(thm)], ['217', '224'])).
% 0.55/0.75  thf('226', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('227', plain,
% 0.55/0.75      ((v1_funct_2 @ 
% 0.55/0.75        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['225', '226'])).
% 0.55/0.75  thf('228', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.55/0.75      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 0.55/0.75  thf('229', plain,
% 0.55/0.75      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.55/0.75        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['227', '228'])).
% 0.55/0.75  thf('230', plain,
% 0.55/0.75      (![X0 : $i]:
% 0.55/0.75         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.55/0.75             (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 0.55/0.75          | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (X0))
% 0.55/0.75          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.75               (k1_zfmisc_1 @ 
% 0.55/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.75          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75          | ~ (v1_funct_1 @ X0))),
% 0.55/0.75      inference('demod', [status(thm)], ['203', '216', '229'])).
% 0.55/0.75  thf('231', plain,
% 0.55/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | ~ (m1_subset_1 @ sk_C @ 
% 0.55/0.75             (k1_zfmisc_1 @ 
% 0.55/0.75              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.55/0.75        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.55/0.75      inference('sup-', [status(thm)], ['186', '230'])).
% 0.55/0.75  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('233', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('234', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('235', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 0.55/0.75  thf('236', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.55/0.75      inference('demod', [status(thm)], ['132', '235'])).
% 0.55/0.75  thf('237', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('238', plain,
% 0.55/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.75         (~ (l1_pre_topc @ X13)
% 0.55/0.75          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.55/0.75          | (v5_pre_topc @ X14 @ X15 @ X13)
% 0.55/0.75          | ~ (m1_subset_1 @ X14 @ 
% 0.55/0.75               (k1_zfmisc_1 @ 
% 0.55/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.55/0.75          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.55/0.75          | ~ (v1_funct_1 @ X14)
% 0.55/0.75          | ~ (l1_pre_topc @ X15))),
% 0.55/0.75      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.55/0.75  thf('239', plain,
% 0.55/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.55/0.75        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.55/0.75        | ~ (l1_pre_topc @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['237', '238'])).
% 0.55/0.75  thf('240', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('242', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('243', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('244', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('245', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['239', '240', '241', '242', '243', '244'])).
% 0.55/0.75  thf('246', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.55/0.75      inference('clc', [status(thm)], ['118', '119'])).
% 0.55/0.75  thf('247', plain,
% 0.55/0.75      ((m1_subset_1 @ sk_C @ 
% 0.55/0.75        (k1_zfmisc_1 @ 
% 0.55/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('248', plain,
% 0.55/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.55/0.75         ((v2_struct_0 @ X19)
% 0.55/0.75          | ~ (l1_struct_0 @ X19)
% 0.55/0.75          | ((k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21)
% 0.55/0.75              != (k2_struct_0 @ X19))
% 0.55/0.75          | ~ (v2_funct_1 @ X21)
% 0.55/0.75          | ((k1_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20) @ 
% 0.55/0.75              (k2_tops_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21))
% 0.55/0.75              = (k2_struct_0 @ X19))
% 0.55/0.75          | ~ (m1_subset_1 @ X21 @ 
% 0.55/0.75               (k1_zfmisc_1 @ 
% 0.55/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.55/0.75          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.55/0.75          | ~ (v1_funct_1 @ X21)
% 0.55/0.75          | ~ (l1_struct_0 @ X20))),
% 0.55/0.75      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.55/0.75  thf('249', plain,
% 0.55/0.75      ((~ (l1_struct_0 @ sk_A)
% 0.55/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.55/0.75        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.55/0.75            = (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75            != (k2_struct_0 @ sk_B))
% 0.55/0.75        | ~ (l1_struct_0 @ sk_B)
% 0.55/0.75        | (v2_struct_0 @ sk_B))),
% 0.55/0.75      inference('sup-', [status(thm)], ['247', '248'])).
% 0.55/0.75  thf('250', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.75  thf('251', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('252', plain,
% 0.55/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('253', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('254', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.55/0.75  thf('255', plain,
% 0.55/0.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)], ['16', '17', '18', '19', '20', '21'])).
% 0.55/0.75  thf('256', plain, ((l1_struct_0 @ sk_B)),
% 0.55/0.75      inference('sup-', [status(thm)], ['35', '36'])).
% 0.55/0.75  thf('257', plain,
% 0.55/0.75      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 0.55/0.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.55/0.75        | (v2_struct_0 @ sk_B))),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['249', '250', '251', '252', '253', '254', '255', '256'])).
% 0.55/0.75  thf('258', plain,
% 0.55/0.75      (((v2_struct_0 @ sk_B)
% 0.55/0.75        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.55/0.75      inference('simplify', [status(thm)], ['257'])).
% 0.55/0.75  thf('259', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('260', plain,
% 0.55/0.75      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.75         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.55/0.75      inference('clc', [status(thm)], ['258', '259'])).
% 0.55/0.75  thf('261', plain,
% 0.55/0.75      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.55/0.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.55/0.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.55/0.75      inference('demod', [status(thm)],
% 0.55/0.75                ['63', '70', '236', '245', '246', '260'])).
% 0.55/0.75  thf('262', plain,
% 0.55/0.75      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.55/0.75        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.55/0.75      inference('simplify', [status(thm)], ['261'])).
% 0.55/0.75  thf('263', plain,
% 0.55/0.75      (~ (v3_tops_2 @ 
% 0.55/0.75          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.55/0.75          sk_B @ sk_A)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('264', plain,
% 0.55/0.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.55/0.75         = (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.75  thf('265', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.55/0.75      inference('demod', [status(thm)], ['263', '264'])).
% 0.55/0.75  thf('266', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.55/0.75      inference('clc', [status(thm)], ['262', '265'])).
% 0.55/0.75  thf('267', plain,
% 0.55/0.75      ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.75      inference('sup-', [status(thm)], ['0', '266'])).
% 0.55/0.75  thf('268', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.75      inference('sup-', [status(thm)], ['123', '124'])).
% 0.55/0.75  thf('269', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.75  thf('270', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.75      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.55/0.75  thf('271', plain, ($false),
% 0.55/0.75      inference('demod', [status(thm)], ['267', '268', '269', '270'])).
% 0.55/0.75  
% 0.55/0.75  % SZS output end Refutation
% 0.55/0.75  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
