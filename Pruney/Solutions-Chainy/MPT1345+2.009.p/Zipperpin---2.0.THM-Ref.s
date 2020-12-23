%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfEjZVap8e

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:30 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 558 expanded)
%              Number of leaves         :   28 ( 184 expanded)
%              Depth                    :   13
%              Number of atoms          : 2365 (13132 expanded)
%              Number of equality atoms :   52 (  81 expanded)
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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

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

thf('6',plain,(
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

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tops_2 @ X6 @ X7 @ X5 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 ) @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('30',plain,(
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

thf('31',plain,(
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

thf('32',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tops_2 @ X6 @ X7 @ X5 )
      | ( v2_funct_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
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

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','35','36','37','46','55','58'])).

thf('60',plain,(
    v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','14','20','29','60','61'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X11 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 )
       != ( k2_struct_0 @ X11 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X12 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) @ X13 ) )
        = ( k2_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('65',plain,
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
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('70',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('72',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','75'])).

thf('77',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
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

thf('82',plain,
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
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('89',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','92'])).

thf('94',plain,(
    ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
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

thf('96',plain,(
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

thf('97',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['40','41','42','43','44','45'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('104',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('109',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('112',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('113',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

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

thf('114',plain,(
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

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('117',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('120',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('121',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('123',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X8 @ X9 @ X10 ) @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('126',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('127',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ X0 )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','121','127'])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['107','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v3_tops_2 @ X6 @ X7 @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['136','137','138','139','140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['94','133','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfEjZVap8e
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 108 iterations in 0.133s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.40/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.59  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.40/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.40/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.40/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.59  thf(t70_tops_2, conjecture,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_pre_topc @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.40/0.59                 ( v3_tops_2 @
% 0.40/0.59                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.40/0.59                   B @ A ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i]:
% 0.40/0.59        ( ( l1_pre_topc @ A ) =>
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.40/0.59              ( ![C:$i]:
% 0.40/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                    ( v1_funct_2 @
% 0.40/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                    ( m1_subset_1 @
% 0.40/0.59                      C @ 
% 0.40/0.59                      ( k1_zfmisc_1 @
% 0.40/0.59                        ( k2_zfmisc_1 @
% 0.40/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.40/0.59                    ( v3_tops_2 @
% 0.40/0.59                      ( k2_tops_2 @
% 0.40/0.59                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.40/0.59                      B @ A ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.40/0.59  thf('0', plain,
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
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((m1_subset_1 @ (k2_tops_2 @ X8 @ X9 @ X10) @ 
% 0.40/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.59          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.59          | ~ (v1_funct_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (m1_subset_1 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           (k1_zfmisc_1 @ 
% 0.40/0.59            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('3', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      ((m1_subset_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3', '4'])).
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
% 0.40/0.59  thf('6', plain,
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
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_B)
% 0.40/0.59        | ~ (v1_funct_1 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59        | ~ (v1_funct_2 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.59        | (v3_tops_2 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_B @ sk_A)
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59             sk_A @ sk_B)
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59             sk_B @ sk_A)
% 0.40/0.59        | ~ (v2_funct_1 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            != (k2_struct_0 @ sk_A))
% 0.40/0.59        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.59  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((v1_funct_1 @ (k2_tops_2 @ X8 @ X9 @ X10))
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.59          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.59          | ~ (v1_funct_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v1_funct_1 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      ((v1_funct_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.59         ((v1_funct_2 @ (k2_tops_2 @ X8 @ X9 @ X10) @ X9 @ X8)
% 0.40/0.59          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.59          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.59          | ~ (v1_funct_1 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v1_funct_2 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.59  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      ((v1_funct_2 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X5)
% 0.40/0.59          | ~ (v3_tops_2 @ X6 @ X7 @ X5)
% 0.40/0.59          | (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6) @ X5 @ 
% 0.40/0.59             X7)
% 0.40/0.59          | ~ (m1_subset_1 @ X6 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.40/0.59          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.40/0.59          | ~ (v1_funct_1 @ X6)
% 0.40/0.59          | ~ (l1_pre_topc @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v5_pre_topc @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_B @ sk_A)
% 0.40/0.59        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.59  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('27', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      ((v5_pre_topc @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59        sk_B @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t63_tops_2, axiom,
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
% 0.40/0.59               ( ( ( ( k2_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.59                 ( v2_funct_1 @
% 0.40/0.59                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.59         (~ (l1_struct_0 @ X14)
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14) @ X16)
% 0.40/0.59              != (k2_struct_0 @ X14))
% 0.40/0.59          | ~ (v2_funct_1 @ X16)
% 0.40/0.59          | (v2_funct_1 @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14) @ X16))
% 0.40/0.59          | ~ (m1_subset_1 @ X16 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))))
% 0.40/0.59          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.40/0.59          | ~ (v1_funct_1 @ X16)
% 0.40/0.59          | ~ (l1_struct_0 @ X15))),
% 0.40/0.59      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v2_funct_1 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(dt_l1_pre_topc, axiom,
% 0.40/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.59  thf('34', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.59  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X5)
% 0.40/0.59          | ~ (v3_tops_2 @ X6 @ X7 @ X5)
% 0.40/0.59          | (v2_funct_1 @ X6)
% 0.40/0.59          | ~ (m1_subset_1 @ X6 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.40/0.59          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.40/0.59          | ~ (v1_funct_1 @ X6)
% 0.40/0.59          | ~ (l1_pre_topc @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (v2_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.59  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('44', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('46', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.59         (~ (l1_pre_topc @ X5)
% 0.40/0.59          | ~ (v3_tops_2 @ X6 @ X7 @ X5)
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6)
% 0.40/0.59              = (k2_struct_0 @ X5))
% 0.40/0.59          | ~ (m1_subset_1 @ X6 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.40/0.59          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.40/0.59          | ~ (v1_funct_1 @ X6)
% 0.40/0.59          | ~ (l1_pre_topc @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            = (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.59  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('53', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.40/0.59  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('57', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.59  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('59', plain,
% 0.40/0.59      (((v2_funct_1 @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['32', '35', '36', '37', '46', '55', '58'])).
% 0.40/0.59  thf('60', plain,
% 0.40/0.59      ((v2_funct_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['59'])).
% 0.40/0.59  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      (((v3_tops_2 @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59         sk_B @ sk_A)
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59             sk_A @ sk_B)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            != (k2_struct_0 @ sk_A))
% 0.40/0.59        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            != (k2_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['7', '8', '14', '20', '29', '60', '61'])).
% 0.40/0.59  thf('63', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t62_tops_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_struct_0 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( ( ( k2_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.59                 ( ( ( k1_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                       ( k2_tops_2 @
% 0.40/0.59                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.40/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                   ( ( k2_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                       ( k2_tops_2 @
% 0.40/0.59                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.40/0.59                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('64', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X11)
% 0.40/0.59          | ~ (l1_struct_0 @ X11)
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13)
% 0.40/0.59              != (k2_struct_0 @ X11))
% 0.40/0.59          | ~ (v2_funct_1 @ X13)
% 0.40/0.59          | ((k1_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12) @ 
% 0.40/0.59              (k2_tops_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13))
% 0.40/0.59              = (k2_struct_0 @ X11))
% 0.40/0.59          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))))
% 0.40/0.59          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 0.40/0.59          | ~ (v1_funct_1 @ X13)
% 0.40/0.59          | ~ (l1_struct_0 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.40/0.59  thf('65', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            = (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['63', '64'])).
% 0.40/0.59  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('68', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.40/0.59  thf('70', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.40/0.59  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('72', plain,
% 0.40/0.59      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59          = (k2_struct_0 @ sk_B))
% 0.40/0.59        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['65', '66', '67', '68', '69', '70', '71'])).
% 0.40/0.59  thf('73', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            = (k2_struct_0 @ sk_B)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['72'])).
% 0.40/0.59  thf('74', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('75', plain,
% 0.40/0.59      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('clc', [status(thm)], ['73', '74'])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      (((v3_tops_2 @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59         sk_B @ sk_A)
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59             sk_A @ sk_B)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            != (k2_struct_0 @ sk_A))
% 0.40/0.59        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.59      inference('demod', [status(thm)], ['62', '75'])).
% 0.40/0.59  thf('77', plain,
% 0.40/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59          != (k2_struct_0 @ sk_A))
% 0.40/0.59        | ~ (v5_pre_topc @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59             sk_A @ sk_B)
% 0.40/0.59        | (v3_tops_2 @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59           sk_B @ sk_A))),
% 0.40/0.59      inference('simplify', [status(thm)], ['76'])).
% 0.40/0.59  thf('78', plain,
% 0.40/0.59      (~ (v3_tops_2 @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.59          sk_B @ sk_A)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('79', plain,
% 0.40/0.59      ((~ (v5_pre_topc @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59           sk_A @ sk_B)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            != (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('clc', [status(thm)], ['77', '78'])).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('81', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X11)
% 0.40/0.59          | ~ (l1_struct_0 @ X11)
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13)
% 0.40/0.59              != (k2_struct_0 @ X11))
% 0.40/0.59          | ~ (v2_funct_1 @ X13)
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X12) @ 
% 0.40/0.59              (k2_tops_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11) @ X13))
% 0.40/0.59              = (k2_struct_0 @ X12))
% 0.40/0.59          | ~ (m1_subset_1 @ X13 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))))
% 0.40/0.59          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 0.40/0.59          | ~ (v1_funct_1 @ X13)
% 0.40/0.59          | ~ (l1_struct_0 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            = (k2_struct_0 @ sk_A))
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['80', '81'])).
% 0.40/0.59  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.40/0.59  thf('87', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.40/0.59  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('89', plain,
% 0.40/0.59      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59          = (k2_struct_0 @ sk_A))
% 0.40/0.59        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['82', '83', '84', '85', '86', '87', '88'])).
% 0.40/0.59  thf('90', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59            = (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['89'])).
% 0.40/0.59  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('92', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.59         = (k2_struct_0 @ sk_A))),
% 0.40/0.59      inference('clc', [status(thm)], ['90', '91'])).
% 0.40/0.59  thf('93', plain,
% 0.40/0.59      ((~ (v5_pre_topc @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59           sk_A @ sk_B)
% 0.40/0.59        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['79', '92'])).
% 0.40/0.59  thf('94', plain,
% 0.40/0.59      (~ (v5_pre_topc @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59          sk_A @ sk_B)),
% 0.40/0.59      inference('simplify', [status(thm)], ['93'])).
% 0.40/0.59  thf('95', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ 
% 0.40/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t64_tops_2, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( l1_struct_0 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.59           ( ![C:$i]:
% 0.40/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.59                 ( m1_subset_1 @
% 0.40/0.59                   C @ 
% 0.40/0.59                   ( k1_zfmisc_1 @
% 0.40/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.59               ( ( ( ( k2_relset_1 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.59                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.59                 ( r2_funct_2 @
% 0.40/0.59                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.59                   ( k2_tops_2 @
% 0.40/0.59                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.59                     ( k2_tops_2 @
% 0.40/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.40/0.59                   C ) ) ) ) ) ) ))).
% 0.40/0.59  thf('96', plain,
% 0.40/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.59         ((v2_struct_0 @ X17)
% 0.40/0.59          | ~ (l1_struct_0 @ X17)
% 0.40/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19)
% 0.40/0.59              != (k2_struct_0 @ X17))
% 0.40/0.59          | ~ (v2_funct_1 @ X19)
% 0.40/0.59          | (r2_funct_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ 
% 0.40/0.59             (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.40/0.59              (k2_tops_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19)) @ 
% 0.40/0.59             X19)
% 0.40/0.59          | ~ (m1_subset_1 @ X19 @ 
% 0.40/0.59               (k1_zfmisc_1 @ 
% 0.40/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 0.40/0.59          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.40/0.59          | ~ (v1_funct_1 @ X19)
% 0.40/0.59          | ~ (l1_struct_0 @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [t64_tops_2])).
% 0.40/0.59  thf('97', plain,
% 0.40/0.59      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.59        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59           sk_C)
% 0.40/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59            != (k2_struct_0 @ sk_B))
% 0.40/0.59        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.59        | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['95', '96'])).
% 0.40/0.59  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('100', plain,
% 0.40/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41', '42', '43', '44', '45'])).
% 0.40/0.59  thf('102', plain,
% 0.40/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.59         = (k2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.40/0.59  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('104', plain,
% 0.40/0.59      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59         sk_C)
% 0.40/0.59        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.59        | (v2_struct_0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)],
% 0.40/0.59                ['97', '98', '99', '100', '101', '102', '103'])).
% 0.40/0.59  thf('105', plain,
% 0.40/0.59      (((v2_struct_0 @ sk_B)
% 0.40/0.59        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59           sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['104'])).
% 0.40/0.59  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('107', plain,
% 0.40/0.59      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.59         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.59        sk_C)),
% 0.40/0.59      inference('clc', [status(thm)], ['105', '106'])).
% 0.40/0.59  thf('108', plain,
% 0.40/0.59      ((m1_subset_1 @ 
% 0.40/0.59        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.40/0.60  thf('109', plain,
% 0.40/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.60         ((m1_subset_1 @ (k2_tops_2 @ X8 @ X9 @ X10) @ 
% 0.40/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.40/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.60          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.60          | ~ (v1_funct_1 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.60  thf('110', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60        | ~ (v1_funct_2 @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.60        | (m1_subset_1 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60           (k1_zfmisc_1 @ 
% 0.40/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['108', '109'])).
% 0.40/0.60  thf('111', plain,
% 0.40/0.60      ((v1_funct_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.60      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.40/0.60  thf('112', plain,
% 0.40/0.60      ((v1_funct_2 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.40/0.60  thf('113', plain,
% 0.40/0.60      ((m1_subset_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.40/0.60  thf(redefinition_r2_funct_2, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.60         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.60       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.40/0.60  thf('114', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.40/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ X3)
% 0.40/0.60          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.40/0.60          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.40/0.60          | ((X0) = (X3))
% 0.40/0.60          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.40/0.60  thf('115', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60             X0)
% 0.40/0.60          | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60              = (X0))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.40/0.60          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60          | ~ (v1_funct_1 @ X0)
% 0.40/0.60          | ~ (v1_funct_1 @ 
% 0.40/0.60               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.40/0.60          | ~ (v1_funct_2 @ 
% 0.40/0.60               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['113', '114'])).
% 0.40/0.60  thf('116', plain,
% 0.40/0.60      ((m1_subset_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.40/0.60  thf('117', plain,
% 0.40/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.60         ((v1_funct_1 @ (k2_tops_2 @ X8 @ X9 @ X10))
% 0.40/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.60          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.60          | ~ (v1_funct_1 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.60  thf('118', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60        | ~ (v1_funct_2 @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.60        | (v1_funct_1 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['116', '117'])).
% 0.40/0.60  thf('119', plain,
% 0.40/0.60      ((v1_funct_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.60      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.40/0.60  thf('120', plain,
% 0.40/0.60      ((v1_funct_2 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.40/0.60  thf('121', plain,
% 0.40/0.60      ((v1_funct_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.40/0.60      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.40/0.60  thf('122', plain,
% 0.40/0.60      ((m1_subset_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.40/0.60  thf('123', plain,
% 0.40/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.60         ((v1_funct_2 @ (k2_tops_2 @ X8 @ X9 @ X10) @ X9 @ X8)
% 0.40/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.40/0.60          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 0.40/0.60          | ~ (v1_funct_1 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.60  thf('124', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60        | ~ (v1_funct_2 @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.40/0.60        | (v1_funct_2 @ 
% 0.40/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['122', '123'])).
% 0.40/0.60  thf('125', plain,
% 0.40/0.60      ((v1_funct_1 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.60      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.40/0.60  thf('126', plain,
% 0.40/0.60      ((v1_funct_2 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.60        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.40/0.60  thf('127', plain,
% 0.40/0.60      ((v1_funct_2 @ 
% 0.40/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.40/0.60  thf('128', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.60             X0)
% 0.40/0.60          | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60              = (X0))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.40/0.60          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60          | ~ (v1_funct_1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['115', '121', '127'])).
% 0.40/0.60  thf('129', plain,
% 0.40/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60        | ~ (m1_subset_1 @ sk_C @ 
% 0.40/0.60             (k1_zfmisc_1 @ 
% 0.40/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.40/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60            = (sk_C)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['107', '128'])).
% 0.40/0.60  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('131', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('132', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('133', plain,
% 0.40/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.60         = (sk_C))),
% 0.40/0.60      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 0.40/0.60  thf('134', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_C @ 
% 0.40/0.60        (k1_zfmisc_1 @ 
% 0.40/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('135', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.60         (~ (l1_pre_topc @ X5)
% 0.40/0.60          | ~ (v3_tops_2 @ X6 @ X7 @ X5)
% 0.40/0.60          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.40/0.60          | ~ (m1_subset_1 @ X6 @ 
% 0.40/0.60               (k1_zfmisc_1 @ 
% 0.40/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.40/0.60          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.40/0.60          | ~ (v1_funct_1 @ X6)
% 0.40/0.60          | ~ (l1_pre_topc @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.60  thf('136', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.60        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.40/0.60        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.60        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['134', '135'])).
% 0.40/0.60  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('139', plain,
% 0.40/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('140', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('141', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('142', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.40/0.60      inference('demod', [status(thm)],
% 0.40/0.60                ['136', '137', '138', '139', '140', '141'])).
% 0.40/0.60  thf('143', plain, ($false),
% 0.40/0.60      inference('demod', [status(thm)], ['94', '133', '142'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
