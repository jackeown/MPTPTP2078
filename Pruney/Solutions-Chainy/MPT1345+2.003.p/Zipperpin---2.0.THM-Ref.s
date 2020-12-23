%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MetGOUj5aX

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  206 (1386 expanded)
%              Number of leaves         :   31 ( 433 expanded)
%              Depth                    :   23
%              Number of atoms          : 2099 (30157 expanded)
%              Number of equality atoms :  100 ( 402 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
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
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X7 @ X9 )
       != X7 )
      | ~ ( v2_funct_1 @ X9 )
      | ( ( k2_tops_2 @ X8 @ X7 @ X9 )
        = ( k2_funct_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X9 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ( v2_funct_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 )
        = ( k2_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 )
       != ( k2_struct_0 @ X12 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 )
       != ( k2_struct_0 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 ) @ X10 @ X12 )
      | ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
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
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X7 @ X9 )
       != X7 )
      | ~ ( v2_funct_1 @ X9 )
      | ( ( k2_tops_2 @ X8 @ X7 @ X9 )
        = ( k2_funct_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X9 ) ) ),
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
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 ) @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('94',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','38'])).

thf('95',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X7 @ X9 )
       != X7 )
      | ~ ( v2_funct_1 @ X9 )
      | ( ( k2_tops_2 @ X8 @ X7 @ X9 )
        = ( k2_funct_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X9 ) ) ),
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
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('103',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('107',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98','107'])).

thf('109',plain,(
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

thf('110',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 )
       != ( k2_struct_0 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 ) )
        = ( k2_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('111',plain,
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
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('119',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('120',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['111','114','115','116','117','118','119','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','124'])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['93','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['102','103'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('130',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['92','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf('133',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['137','138','139','140','141','142'])).

thf('144',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X16 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 )
       != ( k2_struct_0 @ X16 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 ) )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('147',plain,
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
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('153',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30'])).

thf('154',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('155',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152','153','154'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','134','143','144','158'])).

thf('160',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('162',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('165',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('167',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['160','167'])).

thf('169',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['102','103'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['169','170','171','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MetGOUj5aX
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 258 iterations in 0.091s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.56  thf(fc6_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.21/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.56         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.21/0.56  thf(t70_tops_2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.56               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.21/0.56                 ( v3_tops_2 @
% 0.21/0.56                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.21/0.56                   B @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( l1_pre_topc @ A ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                    ( v1_funct_2 @
% 0.21/0.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.56                    ( m1_subset_1 @
% 0.21/0.56                      C @ 
% 0.21/0.56                      ( k1_zfmisc_1 @
% 0.21/0.56                        ( k2_zfmisc_1 @
% 0.21/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.56                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.21/0.56                    ( v3_tops_2 @
% 0.21/0.56                      ( k2_tops_2 @
% 0.21/0.56                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.21/0.56                      B @ A ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_k2_tops_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.21/0.56         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.21/0.56           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k2_tops_2 @ X13 @ X14 @ X15) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.21/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.56          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.21/0.56          | ~ (v1_funct_1 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (m1_subset_1 @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d3_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d4_tops_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.56         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X8 @ X7 @ X9) != (X7))
% 0.21/0.56          | ~ (v2_funct_1 @ X9)
% 0.21/0.56          | ((k2_tops_2 @ X8 @ X7 @ X9) = (k2_funct_1 @ X9))
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.21/0.56          | ~ (v1_funct_2 @ X9 @ X8 @ X7)
% 0.21/0.56          | ~ (v1_funct_1 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.56  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d5_tops_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_pre_topc @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( l1_pre_topc @ B ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.56               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.21/0.56                 ( ( ( k1_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.56                     ( k2_struct_0 @ A ) ) & 
% 0.21/0.56                   ( ( k2_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.56                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.56                   ( v5_pre_topc @
% 0.21/0.56                     ( k2_tops_2 @
% 0.21/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.21/0.56                     B @ A ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.21/0.56          | (v2_funct_1 @ X11)
% 0.21/0.56          | ~ (m1_subset_1 @ X11 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.21/0.56          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.21/0.56          | ~ (v1_funct_1 @ X11)
% 0.21/0.56          | ~ (l1_pre_topc @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (v2_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('19', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['12', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.21/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11)
% 0.21/0.56              = (k2_struct_0 @ X10))
% 0.21/0.56          | ~ (m1_subset_1 @ X11 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.21/0.56          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.21/0.56          | ~ (v1_funct_1 @ X11)
% 0.21/0.56          | ~ (l1_pre_topc @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            = (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('29', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['22', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            = (k2_funct_1 @ sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '32'])).
% 0.21/0.56  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_l1_pre_topc, axiom,
% 0.21/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.56  thf('35', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            = (k2_funct_1 @ sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['33', '36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '4', '5', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X10)
% 0.21/0.56          | ((k1_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11)
% 0.21/0.56              != (k2_struct_0 @ X12))
% 0.21/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11)
% 0.21/0.56              != (k2_struct_0 @ X10))
% 0.21/0.56          | ~ (v2_funct_1 @ X11)
% 0.21/0.56          | ~ (v5_pre_topc @ X11 @ X12 @ X10)
% 0.21/0.56          | ~ (v5_pre_topc @ 
% 0.21/0.56               (k2_tops_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11) @ 
% 0.21/0.56               X10 @ X12)
% 0.21/0.56          | (v3_tops_2 @ X11 @ X12 @ X10)
% 0.21/0.56          | ~ (m1_subset_1 @ X11 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.21/0.56          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.21/0.56          | ~ (v1_funct_1 @ X11)
% 0.21/0.56          | ~ (l1_pre_topc @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.56             (u1_struct_0 @ sk_A))
% 0.21/0.56        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.56        | ~ (v5_pre_topc @ 
% 0.21/0.56             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56              (k2_funct_1 @ sk_C)) @ 
% 0.21/0.56             sk_A @ sk_B)
% 0.21/0.56        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.56        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.21/0.56        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C @ 
% 0.21/0.56         (k1_zfmisc_1 @ 
% 0.21/0.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         ((v1_funct_1 @ (k2_tops_2 @ X13 @ X14 @ X15))
% 0.21/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.56          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.21/0.56          | ~ (v1_funct_1 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | (v1_funct_1 @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((v1_funct_1 @ 
% 0.21/0.56        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50', '55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X8 @ X7 @ X9) != (X7))
% 0.21/0.56          | ~ (v2_funct_1 @ X9)
% 0.21/0.56          | ((k2_tops_2 @ X8 @ X7 @ X9) = (k2_funct_1 @ X9))
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.21/0.56          | ~ (v1_funct_2 @ X9 @ X8 @ X7)
% 0.21/0.56          | ~ (v1_funct_1 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.56  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['65', '66'])).
% 0.21/0.56  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['64', '69'])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.56  thf('72', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['56', '71'])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         ((v1_funct_2 @ (k2_tops_2 @ X13 @ X14 @ X15) @ X14 @ X13)
% 0.21/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.56          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.21/0.56          | ~ (v1_funct_1 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (v1_funct_2 @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.56           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.56  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.56        (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.21/0.56          | (v5_pre_topc @ 
% 0.21/0.56             (k2_tops_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11) @ 
% 0.21/0.56             X10 @ X12)
% 0.21/0.56          | ~ (m1_subset_1 @ X11 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.21/0.56          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.21/0.56          | ~ (v1_funct_1 @ X11)
% 0.21/0.56          | ~ (l1_pre_topc @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (v5_pre_topc @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.56           sk_B @ sk_A)
% 0.21/0.56        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.56  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.56  thf('87', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('89', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['82', '83', '84', '85', '86', '87', '88'])).
% 0.21/0.56  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('91', plain,
% 0.21/0.56      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.56        | ~ (v5_pre_topc @ 
% 0.21/0.56             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56              (k2_funct_1 @ sk_C)) @ 
% 0.21/0.56             sk_A @ sk_B)
% 0.21/0.56        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.21/0.56        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '42', '72', '79', '89', '90'])).
% 0.21/0.56  thf('92', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('93', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.21/0.56  thf('94', plain,
% 0.21/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '4', '5', '38'])).
% 0.21/0.56  thf('95', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X8 @ X7 @ X9) != (X7))
% 0.21/0.56          | ~ (v2_funct_1 @ X9)
% 0.21/0.56          | ((k2_tops_2 @ X8 @ X7 @ X9) = (k2_funct_1 @ X9))
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.21/0.56          | ~ (v1_funct_2 @ X9 @ X8 @ X7)
% 0.21/0.56          | ~ (v1_funct_1 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.56  thf('96', plain,
% 0.21/0.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.56             (u1_struct_0 @ sk_A))
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.21/0.56        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.56  thf('97', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['56', '71'])).
% 0.21/0.56  thf('98', plain,
% 0.21/0.56      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.56        (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.21/0.56  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t65_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.21/0.56  thf('100', plain,
% 0.21/0.56      (![X1 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X1)
% 0.21/0.56          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.21/0.56          | ~ (v1_funct_1 @ X1)
% 0.21/0.56          | ~ (v1_relat_1 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.21/0.56  thf('101', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.56  thf('102', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( v1_relat_1 @ C ) ))).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         ((v1_relat_1 @ X2)
% 0.21/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.56  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.56  thf('105', plain,
% 0.21/0.56      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)) | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['101', '104'])).
% 0.21/0.56  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.56  thf('107', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.56  thf('108', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['96', '97', '98', '107'])).
% 0.21/0.56  thf('109', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t62_tops_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_struct_0 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.56               ( ( ( ( k2_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.56                   ( v2_funct_1 @ C ) ) =>
% 0.21/0.56                 ( ( ( k1_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.56                       ( k2_tops_2 @
% 0.21/0.56                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.56                   ( ( k2_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.56                       ( k2_tops_2 @
% 0.21/0.56                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.56                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('110', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X16)
% 0.21/0.56          | ~ (l1_struct_0 @ X16)
% 0.21/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.21/0.56              != (k2_struct_0 @ X16))
% 0.21/0.56          | ~ (v2_funct_1 @ X18)
% 0.21/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.21/0.56              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.21/0.56              = (k2_struct_0 @ X17))
% 0.21/0.56          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.21/0.56          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.21/0.56          | ~ (v1_funct_1 @ X18)
% 0.21/0.56          | ~ (l1_struct_0 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.21/0.56  thf('111', plain,
% 0.21/0.56      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56            = (k2_struct_0 @ sk_A))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.56  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('113', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.56  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('116', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('117', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.56  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.56  thf('119', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.21/0.56  thf('120', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('121', plain,
% 0.21/0.56      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.21/0.56        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['111', '114', '115', '116', '117', '118', '119', '120'])).
% 0.21/0.56  thf('122', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['121'])).
% 0.21/0.56  thf('123', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('124', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['122', '123'])).
% 0.21/0.56  thf('125', plain,
% 0.21/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['108', '124'])).
% 0.21/0.56  thf('126', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['93', '125'])).
% 0.21/0.56  thf('127', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.56  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.56  thf('130', plain,
% 0.21/0.56      ((((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.21/0.56  thf('131', plain,
% 0.21/0.56      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['92', '130'])).
% 0.21/0.56  thf('132', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.56  thf('133', plain,
% 0.21/0.56      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.21/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['131', '132'])).
% 0.21/0.56  thf('134', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['133'])).
% 0.21/0.56  thf('135', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('136', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (l1_pre_topc @ X10)
% 0.21/0.56          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.21/0.56          | (v5_pre_topc @ X11 @ X12 @ X10)
% 0.21/0.56          | ~ (m1_subset_1 @ X11 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.21/0.56          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.21/0.56          | ~ (v1_funct_1 @ X11)
% 0.21/0.56          | ~ (l1_pre_topc @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.56  thf('137', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.21/0.56        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.56        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['135', '136'])).
% 0.21/0.56  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('140', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('141', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('142', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('143', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['137', '138', '139', '140', '141', '142'])).
% 0.21/0.56  thf('144', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['122', '123'])).
% 0.21/0.56  thf('145', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('146', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X16)
% 0.21/0.56          | ~ (l1_struct_0 @ X16)
% 0.21/0.56          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.21/0.56              != (k2_struct_0 @ X16))
% 0.21/0.56          | ~ (v2_funct_1 @ X18)
% 0.21/0.56          | ((k1_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.21/0.56              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.21/0.56              = (k2_struct_0 @ X16))
% 0.21/0.56          | ~ (m1_subset_1 @ X18 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.21/0.56          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.21/0.56          | ~ (v1_funct_1 @ X18)
% 0.21/0.56          | ~ (l1_struct_0 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.21/0.56  thf('147', plain,
% 0.21/0.56      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56            = (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56            != (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['145', '146'])).
% 0.21/0.56  thf('148', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.56  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('150', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('151', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.56  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.56  thf('153', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26', '27', '28', '29', '30'])).
% 0.21/0.56  thf('154', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('155', plain,
% 0.21/0.56      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 0.21/0.56        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['147', '148', '149', '150', '151', '152', '153', '154'])).
% 0.21/0.56  thf('156', plain,
% 0.21/0.56      (((v2_struct_0 @ sk_B)
% 0.21/0.56        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['155'])).
% 0.21/0.56  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('158', plain,
% 0.21/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('clc', [status(thm)], ['156', '157'])).
% 0.21/0.56  thf('159', plain,
% 0.21/0.56      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.56        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.21/0.56        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('demod', [status(thm)], ['91', '134', '143', '144', '158'])).
% 0.21/0.56  thf('160', plain,
% 0.21/0.56      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.56      inference('simplify', [status(thm)], ['159'])).
% 0.21/0.56  thf('161', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('162', plain,
% 0.21/0.56      (~ (v3_tops_2 @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.56          sk_B @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('163', plain,
% 0.21/0.56      ((~ (v3_tops_2 @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.56           sk_B @ sk_A)
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['161', '162'])).
% 0.21/0.56  thf('164', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('165', plain,
% 0.21/0.56      (~ (v3_tops_2 @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.56          sk_B @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['163', '164'])).
% 0.21/0.56  thf('166', plain,
% 0.21/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.56  thf('167', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['165', '166'])).
% 0.21/0.56  thf('168', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('clc', [status(thm)], ['160', '167'])).
% 0.21/0.56  thf('169', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '168'])).
% 0.21/0.56  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.56  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.21/0.56  thf('173', plain, ($false),
% 0.21/0.56      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
