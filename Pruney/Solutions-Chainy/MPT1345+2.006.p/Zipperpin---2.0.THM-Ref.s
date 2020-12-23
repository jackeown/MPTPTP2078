%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E50DksAkCa

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:29 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  209 (1395 expanded)
%              Number of leaves         :   32 ( 436 expanded)
%              Depth                    :   23
%              Number of atoms          : 2115 (30205 expanded)
%              Number of equality atoms :  100 ( 402 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X8 @ X10 )
       != X8 )
      | ~ ( v2_funct_1 @ X10 )
      | ( ( k2_tops_2 @ X9 @ X8 @ X10 )
        = ( k2_funct_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tops_2 @ X12 @ X13 @ X11 )
      | ( v2_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('22',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tops_2 @ X12 @ X13 @ X11 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 )
        = ( k2_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('32',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 )
       != ( k2_struct_0 @ X13 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 )
       != ( k2_struct_0 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 ) @ X11 @ X13 )
      | ( v3_tops_2 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('41',plain,
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
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X8 @ X10 )
       != X8 )
      | ~ ( v2_funct_1 @ X10 )
      | ( ( k2_tops_2 @ X9 @ X8 @ X10 )
        = ( k2_funct_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('62',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('64',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('67',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('69',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X14 @ X15 @ X16 ) @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('79',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tops_2 @ X12 @ X13 @ X11 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X12 ) @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('87',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['82','83','84','85','86','87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','72','79','89','90'])).

thf('92',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','38'])).

thf('95',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X8 @ X10 )
       != X8 )
      | ~ ( v2_funct_1 @ X10 )
      | ( ( k2_tops_2 @ X9 @ X8 @ X10 )
        = ( k2_funct_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','71'])).

thf('98',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('100',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('105',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','106'])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('109',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98','109'])).

thf('111',plain,(
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

thf('112',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X17 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 )
       != ( k2_struct_0 @ X17 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 ) )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('113',plain,
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
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('121',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('122',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('123',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','116','117','118','119','120','121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','126'])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['93','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['104','105'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('132',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['92','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('135',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tops_2 @ X12 @ X13 @ X11 )
      | ( v5_pre_topc @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('139',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['139','140','141','142','143','144'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X17 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 )
       != ( k2_struct_0 @ X17 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 ) )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('149',plain,
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
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('155',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('156',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('157',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['149','150','151','152','153','154','155','156'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','136','145','146','160'])).

thf('162',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('164',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('167',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('169',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['162','169'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['104','105'])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['171','172','173','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E50DksAkCa
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:32:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 258 iterations in 0.126s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.62  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.40/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.62  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.40/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.62  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.40/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.62  thf(fc6_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.40/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.62         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v2_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.40/0.62  thf(t70_tops_2, conjecture,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( l1_pre_topc @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.40/0.62           ( ![C:$i]:
% 0.40/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.62                 ( m1_subset_1 @
% 0.40/0.62                   C @ 
% 0.40/0.62                   ( k1_zfmisc_1 @
% 0.40/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.62               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.40/0.62                 ( v3_tops_2 @
% 0.40/0.62                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.40/0.62                   B @ A ) ) ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i]:
% 0.40/0.62        ( ( l1_pre_topc @ A ) =>
% 0.40/0.62          ( ![B:$i]:
% 0.40/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.40/0.62              ( ![C:$i]:
% 0.40/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.62                    ( v1_funct_2 @
% 0.40/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.62                    ( m1_subset_1 @
% 0.40/0.62                      C @ 
% 0.40/0.62                      ( k1_zfmisc_1 @
% 0.40/0.62                        ( k2_zfmisc_1 @
% 0.40/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.62                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.40/0.62                    ( v3_tops_2 @
% 0.40/0.62                      ( k2_tops_2 @
% 0.40/0.62                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.40/0.62                      B @ A ) ) ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(dt_k2_tops_2, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.62       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.40/0.62         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.40/0.62         ( m1_subset_1 @
% 0.40/0.62           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.40/0.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.62         ((m1_subset_1 @ (k2_tops_2 @ X14 @ X15 @ X16) @ 
% 0.40/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.40/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.40/0.62          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.40/0.62          | ~ (v1_funct_1 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | (m1_subset_1 @ 
% 0.40/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.62           (k1_zfmisc_1 @ 
% 0.40/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(d3_struct_0, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X6 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(d4_tops_2, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.62         (((k2_relset_1 @ X9 @ X8 @ X10) != (X8))
% 0.40/0.62          | ~ (v2_funct_1 @ X10)
% 0.40/0.62          | ((k2_tops_2 @ X9 @ X8 @ X10) = (k2_funct_1 @ X10))
% 0.40/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.40/0.62          | ~ (v1_funct_2 @ X10 @ X9 @ X8)
% 0.40/0.62          | ~ (v1_funct_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (u1_struct_0 @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.62  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62          = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (u1_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(d5_tops_2, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( l1_pre_topc @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( l1_pre_topc @ B ) =>
% 0.40/0.62           ( ![C:$i]:
% 0.40/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.62                 ( m1_subset_1 @
% 0.40/0.62                   C @ 
% 0.40/0.62                   ( k1_zfmisc_1 @
% 0.40/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.62               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.40/0.62                 ( ( ( k1_relset_1 @
% 0.40/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.62                     ( k2_struct_0 @ A ) ) & 
% 0.40/0.62                   ( ( k2_relset_1 @
% 0.40/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.62                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.40/0.62                   ( v5_pre_topc @
% 0.40/0.62                     ( k2_tops_2 @
% 0.40/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.40/0.62                     B @ A ) ) ) ) ) ) ) ))).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ X11)
% 0.40/0.62          | ~ (v3_tops_2 @ X12 @ X13 @ X11)
% 0.40/0.62          | (v2_funct_1 @ X12)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.40/0.62          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.40/0.62          | ~ (v1_funct_1 @ X12)
% 0.40/0.62          | ~ (l1_pre_topc @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | (v2_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('19', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('21', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62          = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (u1_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['12', '21'])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ X11)
% 0.40/0.62          | ~ (v3_tops_2 @ X12 @ X13 @ X11)
% 0.40/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X12)
% 0.40/0.62              = (k2_struct_0 @ X11))
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.40/0.62          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.40/0.62          | ~ (v1_funct_1 @ X12)
% 0.40/0.62          | ~ (l1_pre_topc @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            = (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.62  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('29', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62          = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['22', '31'])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            = (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '32'])).
% 0.40/0.62  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(dt_l1_pre_topc, axiom,
% 0.40/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.62  thf('35', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('37', plain,
% 0.40/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            = (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['33', '36'])).
% 0.40/0.62  thf('38', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.62  thf('39', plain,
% 0.40/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['3', '4', '5', '38'])).
% 0.40/0.62  thf('40', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ X11)
% 0.40/0.62          | ((k1_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X12)
% 0.40/0.62              != (k2_struct_0 @ X13))
% 0.40/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X12)
% 0.40/0.62              != (k2_struct_0 @ X11))
% 0.40/0.62          | ~ (v2_funct_1 @ X12)
% 0.40/0.62          | ~ (v5_pre_topc @ X12 @ X13 @ X11)
% 0.40/0.62          | ~ (v5_pre_topc @ 
% 0.40/0.62               (k2_tops_2 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X12) @ 
% 0.40/0.62               X11 @ X13)
% 0.40/0.62          | (v3_tops_2 @ X12 @ X13 @ X11)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.40/0.62          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.40/0.62          | ~ (v1_funct_1 @ X12)
% 0.40/0.62          | ~ (l1_pre_topc @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.40/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.62             (u1_struct_0 @ sk_A))
% 0.40/0.62        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.40/0.62        | ~ (v5_pre_topc @ 
% 0.40/0.62             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62              (k2_funct_1 @ sk_C)) @ 
% 0.40/0.62             sk_A @ sk_B)
% 0.40/0.62        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.40/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.40/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.62  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      (![X6 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('45', plain,
% 0.40/0.62      (((m1_subset_1 @ sk_C @ 
% 0.40/0.62         (k1_zfmisc_1 @ 
% 0.40/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['43', '44'])).
% 0.40/0.62  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('47', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.62  thf('48', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.62         ((v1_funct_1 @ (k2_tops_2 @ X14 @ X15 @ X16))
% 0.40/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.40/0.62          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.40/0.62          | ~ (v1_funct_1 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.62  thf('49', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.62        | (v1_funct_1 @ 
% 0.40/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.62  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      (![X6 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('52', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('53', plain,
% 0.40/0.62      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['51', '52'])).
% 0.40/0.62  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('55', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.62  thf('56', plain,
% 0.40/0.62      ((v1_funct_1 @ 
% 0.40/0.62        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['49', '50', '55'])).
% 0.40/0.62  thf('57', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.40/0.62  thf('58', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.62         (((k2_relset_1 @ X9 @ X8 @ X10) != (X8))
% 0.40/0.62          | ~ (v2_funct_1 @ X10)
% 0.40/0.62          | ((k2_tops_2 @ X9 @ X8 @ X10) = (k2_funct_1 @ X10))
% 0.40/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.40/0.62          | ~ (v1_funct_2 @ X10 @ X9 @ X8)
% 0.40/0.62          | ~ (v1_funct_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.62  thf('59', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['57', '58'])).
% 0.40/0.62  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('61', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.40/0.62  thf('62', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62          = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.40/0.62  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.40/0.62  thf('64', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62          = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.40/0.62  thf('65', plain,
% 0.40/0.62      (![X6 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('66', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.40/0.62  thf('67', plain,
% 0.40/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62          = (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['65', '66'])).
% 0.40/0.62  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('69', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['67', '68'])).
% 0.40/0.62  thf('70', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62          = (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['64', '69'])).
% 0.40/0.62  thf('71', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.40/0.62  thf('72', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['56', '71'])).
% 0.40/0.62  thf('73', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('74', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.62         ((v1_funct_2 @ (k2_tops_2 @ X14 @ X15 @ X16) @ X15 @ X14)
% 0.40/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.40/0.62          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.40/0.62          | ~ (v1_funct_1 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.40/0.62  thf('75', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | (v1_funct_2 @ 
% 0.40/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.62           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.40/0.62  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('77', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('78', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.62  thf('79', plain,
% 0.40/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.62        (u1_struct_0 @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.40/0.62  thf('80', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('81', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ X11)
% 0.40/0.62          | ~ (v3_tops_2 @ X12 @ X13 @ X11)
% 0.40/0.62          | (v5_pre_topc @ 
% 0.40/0.62             (k2_tops_2 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ X12) @ 
% 0.40/0.62             X11 @ X13)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.40/0.62          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.40/0.62          | ~ (v1_funct_1 @ X12)
% 0.40/0.62          | ~ (l1_pre_topc @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.62  thf('82', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | (v5_pre_topc @ 
% 0.40/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.62           sk_B @ sk_A)
% 0.40/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.40/0.62  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('85', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('86', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.62  thf('87', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('89', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.40/0.62      inference('demod', [status(thm)],
% 0.40/0.62                ['82', '83', '84', '85', '86', '87', '88'])).
% 0.40/0.62  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('91', plain,
% 0.40/0.62      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.40/0.62        | ~ (v5_pre_topc @ 
% 0.40/0.62             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62              (k2_funct_1 @ sk_C)) @ 
% 0.40/0.62             sk_A @ sk_B)
% 0.40/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.40/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['41', '42', '72', '79', '89', '90'])).
% 0.40/0.62  thf('92', plain,
% 0.40/0.62      (![X6 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('93', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v2_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.40/0.62  thf('94', plain,
% 0.40/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.40/0.62      inference('demod', [status(thm)], ['3', '4', '5', '38'])).
% 0.40/0.62  thf('95', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.62         (((k2_relset_1 @ X9 @ X8 @ X10) != (X8))
% 0.40/0.62          | ~ (v2_funct_1 @ X10)
% 0.40/0.62          | ((k2_tops_2 @ X9 @ X8 @ X10) = (k2_funct_1 @ X10))
% 0.40/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.40/0.62          | ~ (v1_funct_2 @ X10 @ X9 @ X8)
% 0.40/0.62          | ~ (v1_funct_1 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.62  thf('96', plain,
% 0.40/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.62             (u1_struct_0 @ sk_A))
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.40/0.62  thf('97', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['56', '71'])).
% 0.40/0.62  thf('98', plain,
% 0.40/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.62        (u1_struct_0 @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.40/0.62  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t65_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.40/0.62  thf('100', plain,
% 0.40/0.62      (![X5 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X5)
% 0.40/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.40/0.62          | ~ (v1_funct_1 @ X5)
% 0.40/0.62          | ~ (v1_relat_1 @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.62  thf('101', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.40/0.62  thf('102', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(cc2_relat_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.62  thf('103', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.62          | (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.62  thf('104', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ 
% 0.40/0.62           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.40/0.62        | (v1_relat_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['102', '103'])).
% 0.40/0.62  thf(fc6_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.62  thf('105', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.62  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['104', '105'])).
% 0.40/0.62  thf('107', plain,
% 0.40/0.62      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)) | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['101', '106'])).
% 0.40/0.62  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.40/0.62  thf('109', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['107', '108'])).
% 0.40/0.62  thf('110', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['96', '97', '98', '109'])).
% 0.40/0.62  thf('111', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t62_tops_2, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( l1_struct_0 @ A ) =>
% 0.40/0.62       ( ![B:$i]:
% 0.40/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.62           ( ![C:$i]:
% 0.40/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.62                 ( m1_subset_1 @
% 0.40/0.62                   C @ 
% 0.40/0.62                   ( k1_zfmisc_1 @
% 0.40/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.62               ( ( ( ( k2_relset_1 @
% 0.40/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.62                 ( ( ( k1_relset_1 @
% 0.40/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.62                       ( k2_tops_2 @
% 0.40/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.40/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.62                   ( ( k2_relset_1 @
% 0.40/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.62                       ( k2_tops_2 @
% 0.40/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.40/0.62                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.40/0.62  thf('112', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((v2_struct_0 @ X17)
% 0.40/0.62          | ~ (l1_struct_0 @ X17)
% 0.40/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19)
% 0.40/0.62              != (k2_struct_0 @ X17))
% 0.40/0.62          | ~ (v2_funct_1 @ X19)
% 0.40/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.40/0.62              (k2_tops_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19))
% 0.40/0.62              = (k2_struct_0 @ X18))
% 0.40/0.62          | ~ (m1_subset_1 @ X19 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 0.40/0.62          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.40/0.62          | ~ (v1_funct_1 @ X19)
% 0.40/0.62          | ~ (l1_struct_0 @ X18))),
% 0.40/0.62      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.40/0.62  thf('113', plain,
% 0.40/0.62      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.62            = (k2_struct_0 @ sk_A))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.62        | (v2_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['111', '112'])).
% 0.40/0.62  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('115', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.62  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.40/0.62  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('118', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('119', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.62  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.40/0.62  thf('121', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.40/0.62  thf('122', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('123', plain,
% 0.40/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.40/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.62        | (v2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)],
% 0.40/0.62                ['113', '116', '117', '118', '119', '120', '121', '122'])).
% 0.40/0.62  thf('124', plain,
% 0.40/0.62      (((v2_struct_0 @ sk_B)
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['123'])).
% 0.40/0.62  thf('125', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('126', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.40/0.62      inference('clc', [status(thm)], ['124', '125'])).
% 0.40/0.62  thf('127', plain,
% 0.40/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['110', '126'])).
% 0.40/0.62  thf('128', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['93', '127'])).
% 0.40/0.62  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['104', '105'])).
% 0.40/0.62  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.40/0.62  thf('132', plain,
% 0.40/0.62      ((((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.40/0.62  thf('133', plain,
% 0.40/0.62      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['92', '132'])).
% 0.40/0.62  thf('134', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.40/0.62  thf('135', plain,
% 0.40/0.62      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.40/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['133', '134'])).
% 0.40/0.62  thf('136', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['135'])).
% 0.40/0.62  thf('137', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('138', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (l1_pre_topc @ X11)
% 0.40/0.62          | ~ (v3_tops_2 @ X12 @ X13 @ X11)
% 0.40/0.62          | (v5_pre_topc @ X12 @ X13 @ X11)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.40/0.62          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.40/0.62          | ~ (v1_funct_1 @ X12)
% 0.40/0.62          | ~ (l1_pre_topc @ X13))),
% 0.40/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.40/0.62  thf('139', plain,
% 0.40/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.40/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['137', '138'])).
% 0.40/0.62  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('142', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('143', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('144', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('145', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.40/0.62      inference('demod', [status(thm)],
% 0.40/0.62                ['139', '140', '141', '142', '143', '144'])).
% 0.40/0.62  thf('146', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.40/0.62      inference('clc', [status(thm)], ['124', '125'])).
% 0.40/0.62  thf('147', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('148', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((v2_struct_0 @ X17)
% 0.40/0.62          | ~ (l1_struct_0 @ X17)
% 0.40/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19)
% 0.40/0.62              != (k2_struct_0 @ X17))
% 0.40/0.62          | ~ (v2_funct_1 @ X19)
% 0.40/0.62          | ((k1_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.40/0.62              (k2_tops_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19))
% 0.40/0.62              = (k2_struct_0 @ X17))
% 0.40/0.62          | ~ (m1_subset_1 @ X19 @ 
% 0.40/0.62               (k1_zfmisc_1 @ 
% 0.40/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 0.40/0.62          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.40/0.62          | ~ (v1_funct_1 @ X19)
% 0.40/0.62          | ~ (l1_struct_0 @ X18))),
% 0.40/0.62      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.40/0.62  thf('149', plain,
% 0.40/0.62      ((~ (l1_struct_0 @ sk_A)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.40/0.62            = (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62            != (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.40/0.62        | (v2_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['147', '148'])).
% 0.40/0.62  thf('150', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['114', '115'])).
% 0.40/0.62  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('152', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('153', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.62  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.40/0.62  thf('155', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.40/0.62  thf('156', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('157', plain,
% 0.40/0.62      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 0.40/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.40/0.62        | (v2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)],
% 0.40/0.62                ['149', '150', '151', '152', '153', '154', '155', '156'])).
% 0.40/0.62  thf('158', plain,
% 0.40/0.62      (((v2_struct_0 @ sk_B)
% 0.40/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['157'])).
% 0.40/0.62  thf('159', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('160', plain,
% 0.40/0.62      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.62         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('clc', [status(thm)], ['158', '159'])).
% 0.40/0.62  thf('161', plain,
% 0.40/0.62      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.40/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.40/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['91', '136', '145', '146', '160'])).
% 0.40/0.62  thf('162', plain,
% 0.40/0.62      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.40/0.62      inference('simplify', [status(thm)], ['161'])).
% 0.40/0.62  thf('163', plain,
% 0.40/0.62      (![X6 : $i]:
% 0.40/0.62         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.62  thf('164', plain,
% 0.40/0.62      (~ (v3_tops_2 @ 
% 0.40/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.62          sk_B @ sk_A)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('165', plain,
% 0.40/0.62      ((~ (v3_tops_2 @ 
% 0.40/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.62           sk_B @ sk_A)
% 0.40/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['163', '164'])).
% 0.40/0.62  thf('166', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('167', plain,
% 0.40/0.62      (~ (v3_tops_2 @ 
% 0.40/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.40/0.62          sk_B @ sk_A)),
% 0.40/0.62      inference('demod', [status(thm)], ['165', '166'])).
% 0.40/0.62  thf('168', plain,
% 0.40/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.40/0.62  thf('169', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.40/0.62      inference('demod', [status(thm)], ['167', '168'])).
% 0.40/0.62  thf('170', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('clc', [status(thm)], ['162', '169'])).
% 0.40/0.62  thf('171', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '170'])).
% 0.40/0.62  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['104', '105'])).
% 0.40/0.62  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('174', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.40/0.62  thf('175', plain, ($false),
% 0.40/0.62      inference('demod', [status(thm)], ['171', '172', '173', '174'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
