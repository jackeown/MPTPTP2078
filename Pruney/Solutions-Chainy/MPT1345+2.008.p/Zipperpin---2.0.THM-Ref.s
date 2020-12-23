%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5VjRT1JTUc

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:30 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  207 (1403 expanded)
%              Number of leaves         :   32 ( 441 expanded)
%              Depth                    :   20
%              Number of atoms          : 2206 (31872 expanded)
%              Number of equality atoms :  110 ( 386 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
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

thf('3',plain,(
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

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('16',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
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

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('26',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relset_1 @ X7 @ X6 @ X5 )
       != X6 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X5 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('47',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
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

thf('50',plain,
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
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relset_1 @ X7 @ X6 @ X5 )
       != X6 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('60',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('62',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('65',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relset_1 @ X7 @ X6 @ X5 )
       != X6 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X5 ) @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('77',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('80',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X14 ) @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('89',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','66','81','91','92'])).

thf('94',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('96',plain,(
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

thf('97',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('99',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('101',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('110',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99','110'])).

thf('112',plain,(
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

thf('113',plain,(
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

thf('114',plain,
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
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('122',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('123',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('124',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','117','118','119','120','121','122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','127'])).

thf('129',plain,(
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

thf('130',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 )
       != ( k2_struct_0 @ X19 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('131',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('137',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('139',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136','137','138'])).

thf('140',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','140'])).

thf('142',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['94','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('144',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v3_tops_2 @ X14 @ X15 @ X13 )
      | ( v5_pre_topc @ X14 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('148',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['148','149','150','151','152','153'])).

thf('155',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['139'])).

thf('156',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('157',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
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

thf('159',plain,
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
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10','11','12','13','14'])).

thf('165',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('166',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164','165','166'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','145','154','155','156','170'])).

thf('172',plain,(
    v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['33','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5VjRT1JTUc
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:55:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 240 iterations in 0.138s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.39/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.62  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.39/0.62  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.39/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.62  thf(t70_tops_2, conjecture,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( l1_pre_topc @ A ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.62                 ( m1_subset_1 @
% 0.39/0.62                   C @ 
% 0.39/0.62                   ( k1_zfmisc_1 @
% 0.39/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.62               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.39/0.62                 ( v3_tops_2 @
% 0.39/0.62                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.39/0.62                   B @ A ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i]:
% 0.39/0.62        ( ( l1_pre_topc @ A ) =>
% 0.39/0.62          ( ![B:$i]:
% 0.39/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.39/0.62              ( ![C:$i]:
% 0.39/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62                    ( v1_funct_2 @
% 0.39/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.62                    ( m1_subset_1 @
% 0.39/0.62                      C @ 
% 0.39/0.62                      ( k1_zfmisc_1 @
% 0.39/0.62                        ( k2_zfmisc_1 @
% 0.39/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.62                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.39/0.62                    ( v3_tops_2 @
% 0.39/0.62                      ( k2_tops_2 @
% 0.39/0.62                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.39/0.62                      B @ A ) ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      (~ (v3_tops_2 @ 
% 0.39/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.39/0.62          sk_B @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d3_struct_0, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X8 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d4_tops_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.39/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.39/0.62          | ~ (v2_funct_1 @ X12)
% 0.39/0.62          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.39/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.39/0.62          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.39/0.62          | ~ (v1_funct_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            = (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d5_tops_2, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( l1_pre_topc @ A ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( l1_pre_topc @ B ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.62                 ( m1_subset_1 @
% 0.39/0.62                   C @ 
% 0.39/0.62                   ( k1_zfmisc_1 @
% 0.39/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.62               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.39/0.62                 ( ( ( k1_relset_1 @
% 0.39/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.62                     ( k2_struct_0 @ A ) ) & 
% 0.39/0.62                   ( ( k2_relset_1 @
% 0.39/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.62                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.39/0.62                   ( v5_pre_topc @
% 0.39/0.62                     ( k2_tops_2 @
% 0.39/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.39/0.62                     B @ A ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (~ (l1_pre_topc @ X13)
% 0.39/0.62          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.39/0.62          | (v2_funct_1 @ X14)
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.39/0.62          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.39/0.62          | ~ (v1_funct_1 @ X14)
% 0.39/0.62          | ~ (l1_pre_topc @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | (v2_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('13', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('15', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62          = (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['4', '5', '6', '15'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (~ (l1_pre_topc @ X13)
% 0.39/0.62          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.39/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14)
% 0.39/0.62              = (k2_struct_0 @ X13))
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.39/0.62          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.39/0.62          | ~ (v1_funct_1 @ X14)
% 0.39/0.62          | ~ (l1_pre_topc @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            = (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.62  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('23', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62          = (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['16', '25'])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            = (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '26'])).
% 0.39/0.62  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(dt_l1_pre_topc, axiom,
% 0.39/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.62  thf('29', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.62  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            = (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['27', '30'])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.62  thf('33', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '32'])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X8 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t31_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.39/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.39/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.39/0.62           ( m1_subset_1 @
% 0.39/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X5)
% 0.39/0.62          | ((k2_relset_1 @ X7 @ X6 @ X5) != (X6))
% 0.39/0.62          | (m1_subset_1 @ (k2_funct_1 @ X5) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.39/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.39/0.62          | ~ (v1_funct_2 @ X5 @ X7 @ X6)
% 0.39/0.62          | ~ (v1_funct_1 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.62  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.39/0.62  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['34', '44'])).
% 0.39/0.62  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (~ (l1_pre_topc @ X13)
% 0.39/0.62          | ((k1_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14)
% 0.39/0.62              != (k2_struct_0 @ X15))
% 0.39/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14)
% 0.39/0.62              != (k2_struct_0 @ X13))
% 0.39/0.62          | ~ (v2_funct_1 @ X14)
% 0.39/0.62          | ~ (v5_pre_topc @ X14 @ X15 @ X13)
% 0.39/0.62          | ~ (v5_pre_topc @ 
% 0.39/0.62               (k2_tops_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14) @ 
% 0.39/0.62               X13 @ X15)
% 0.39/0.62          | (v3_tops_2 @ X14 @ X15 @ X13)
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.39/0.62          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.39/0.62          | ~ (v1_funct_1 @ X14)
% 0.39/0.62          | ~ (l1_pre_topc @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      ((~ (l1_pre_topc @ sk_B)
% 0.39/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62             (u1_struct_0 @ sk_A))
% 0.39/0.62        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v5_pre_topc @ 
% 0.39/0.62             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62              (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62             sk_A @ sk_B)
% 0.39/0.62        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.39/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.62  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X8 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X5)
% 0.39/0.62          | ((k2_relset_1 @ X7 @ X6 @ X5) != (X6))
% 0.39/0.62          | (v1_funct_1 @ (k2_funct_1 @ X5))
% 0.39/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.39/0.62          | ~ (v1_funct_2 @ X5 @ X7 @ X6)
% 0.39/0.62          | ~ (v1_funct_1 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.62  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.39/0.62  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['60', '61'])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['52', '62'])).
% 0.39/0.62  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['63', '64'])).
% 0.39/0.62  thf('66', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['65'])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      (![X8 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X5)
% 0.39/0.62          | ((k2_relset_1 @ X7 @ X6 @ X5) != (X6))
% 0.39/0.62          | (v1_funct_2 @ (k2_funct_1 @ X5) @ X6 @ X7)
% 0.39/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.39/0.62          | ~ (v1_funct_2 @ X5 @ X7 @ X6)
% 0.39/0.62          | ~ (v1_funct_1 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62           (u1_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62         (u1_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.39/0.62  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62         (u1_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['73', '74'])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.39/0.62  thf('77', plain,
% 0.39/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62         (u1_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['75', '76'])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62           (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['67', '77'])).
% 0.39/0.62  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62           (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62        (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('simplify', [status(thm)], ['80'])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (~ (l1_pre_topc @ X13)
% 0.39/0.62          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.39/0.62          | (v5_pre_topc @ 
% 0.39/0.62             (k2_tops_2 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ X14) @ 
% 0.39/0.62             X13 @ X15)
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.39/0.62          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.39/0.62          | ~ (v1_funct_1 @ X14)
% 0.39/0.62          | ~ (l1_pre_topc @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.39/0.62  thf('84', plain,
% 0.39/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | (v5_pre_topc @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.39/0.62           sk_B @ sk_A)
% 0.39/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['82', '83'])).
% 0.39/0.62  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('88', plain,
% 0.39/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.62  thf('89', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('91', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['84', '85', '86', '87', '88', '89', '90'])).
% 0.39/0.62  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('93', plain,
% 0.39/0.62      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v5_pre_topc @ 
% 0.39/0.62             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62              (k2_funct_1 @ sk_C)) @ 
% 0.39/0.62             sk_A @ sk_B)
% 0.39/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.39/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['50', '51', '66', '81', '91', '92'])).
% 0.39/0.62  thf('94', plain,
% 0.39/0.62      (![X8 : $i]:
% 0.39/0.62         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.62  thf('95', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.39/0.62  thf('96', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X11 @ X10 @ X12) != (X10))
% 0.39/0.62          | ~ (v2_funct_1 @ X12)
% 0.39/0.62          | ((k2_tops_2 @ X11 @ X10 @ X12) = (k2_funct_1 @ X12))
% 0.39/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X10)))
% 0.39/0.62          | ~ (v1_funct_2 @ X12 @ X11 @ X10)
% 0.39/0.62          | ~ (v1_funct_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.62  thf('97', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62             (u1_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['95', '96'])).
% 0.39/0.62  thf('98', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['65'])).
% 0.39/0.62  thf('99', plain,
% 0.39/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.62        (u1_struct_0 @ sk_A))),
% 0.39/0.62      inference('simplify', [status(thm)], ['80'])).
% 0.39/0.62  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t65_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.39/0.62  thf('101', plain,
% 0.39/0.62      (![X4 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X4)
% 0.39/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.39/0.62          | ~ (v1_funct_1 @ X4)
% 0.39/0.62          | ~ (v1_relat_1 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.39/0.62  thf('102', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['100', '101'])).
% 0.39/0.62  thf('103', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc2_relat_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ A ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.62  thf('104', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.39/0.62          | (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.62  thf('105', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ 
% 0.39/0.62           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.39/0.62        | (v1_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['103', '104'])).
% 0.39/0.62  thf(fc6_relat_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.62  thf('106', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.62  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '106'])).
% 0.39/0.62  thf('108', plain,
% 0.39/0.62      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)) | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['102', '107'])).
% 0.39/0.62  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('110', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['108', '109'])).
% 0.39/0.62  thf('111', plain,
% 0.39/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.39/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['97', '98', '99', '110'])).
% 0.39/0.62  thf('112', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t62_tops_2, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( l1_struct_0 @ A ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.62                 ( m1_subset_1 @
% 0.39/0.62                   C @ 
% 0.39/0.62                   ( k1_zfmisc_1 @
% 0.39/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.62               ( ( ( ( k2_relset_1 @
% 0.39/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.39/0.62                 ( ( ( k1_relset_1 @
% 0.39/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.62                       ( k2_tops_2 @
% 0.39/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.39/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.62                   ( ( k2_relset_1 @
% 0.39/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.62                       ( k2_tops_2 @
% 0.39/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.39/0.62                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('113', plain,
% 0.39/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.62         ((v2_struct_0 @ X16)
% 0.39/0.62          | ~ (l1_struct_0 @ X16)
% 0.39/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.39/0.62              != (k2_struct_0 @ X16))
% 0.39/0.62          | ~ (v2_funct_1 @ X18)
% 0.39/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.39/0.62              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.39/0.62              = (k2_struct_0 @ X17))
% 0.39/0.62          | ~ (m1_subset_1 @ X18 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.39/0.62          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.39/0.62          | ~ (v1_funct_1 @ X18)
% 0.39/0.62          | ~ (l1_struct_0 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.39/0.62  thf('114', plain,
% 0.39/0.62      ((~ (l1_struct_0 @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.39/0.62            = (k2_struct_0 @ sk_A))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.62        | (v2_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['112', '113'])).
% 0.39/0.62  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('116', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.62  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('sup-', [status(thm)], ['115', '116'])).
% 0.39/0.62  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('119', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('120', plain,
% 0.39/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.62  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('122', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.39/0.62  thf('123', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('124', plain,
% 0.39/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | (v2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['114', '117', '118', '119', '120', '121', '122', '123'])).
% 0.39/0.62  thf('125', plain,
% 0.39/0.62      (((v2_struct_0 @ sk_B)
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['124'])).
% 0.39/0.62  thf('126', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('127', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('clc', [status(thm)], ['125', '126'])).
% 0.39/0.62  thf('128', plain,
% 0.39/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.39/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['111', '127'])).
% 0.39/0.62  thf('129', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t63_tops_2, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( l1_struct_0 @ A ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( l1_struct_0 @ B ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.62                 ( m1_subset_1 @
% 0.39/0.62                   C @ 
% 0.39/0.62                   ( k1_zfmisc_1 @
% 0.39/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.62               ( ( ( ( k2_relset_1 @
% 0.39/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.39/0.62                 ( v2_funct_1 @
% 0.39/0.62                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('130', plain,
% 0.39/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.62         (~ (l1_struct_0 @ X19)
% 0.39/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21)
% 0.39/0.62              != (k2_struct_0 @ X19))
% 0.39/0.62          | ~ (v2_funct_1 @ X21)
% 0.39/0.62          | (v2_funct_1 @ 
% 0.39/0.62             (k2_tops_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21))
% 0.39/0.62          | ~ (m1_subset_1 @ X21 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.39/0.62          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.39/0.62          | ~ (v1_funct_1 @ X21)
% 0.39/0.62          | ~ (l1_struct_0 @ X20))),
% 0.39/0.62      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.39/0.62  thf('131', plain,
% 0.39/0.62      ((~ (l1_struct_0 @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | (v2_funct_1 @ 
% 0.39/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['129', '130'])).
% 0.39/0.62  thf('132', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('sup-', [status(thm)], ['115', '116'])).
% 0.39/0.62  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('134', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('135', plain,
% 0.39/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.62  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('137', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.39/0.62  thf('138', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('139', plain,
% 0.39/0.62      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['131', '132', '133', '134', '135', '136', '137', '138'])).
% 0.39/0.62  thf('140', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['139'])).
% 0.39/0.62  thf('141', plain,
% 0.39/0.62      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.39/0.62        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['128', '140'])).
% 0.39/0.62  thf('142', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['94', '141'])).
% 0.39/0.62  thf('143', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('sup-', [status(thm)], ['115', '116'])).
% 0.39/0.62  thf('144', plain,
% 0.39/0.62      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['142', '143'])).
% 0.39/0.62  thf('145', plain,
% 0.39/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['144'])).
% 0.39/0.62  thf('146', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('147', plain,
% 0.39/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (~ (l1_pre_topc @ X13)
% 0.39/0.62          | ~ (v3_tops_2 @ X14 @ X15 @ X13)
% 0.39/0.62          | (v5_pre_topc @ X14 @ X15 @ X13)
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.39/0.62          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.39/0.62          | ~ (v1_funct_1 @ X14)
% 0.39/0.62          | ~ (l1_pre_topc @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.39/0.62  thf('148', plain,
% 0.39/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.62        | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['146', '147'])).
% 0.39/0.62  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('151', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('152', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('153', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('154', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['148', '149', '150', '151', '152', '153'])).
% 0.39/0.62  thf('155', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['139'])).
% 0.39/0.62  thf('156', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.39/0.62      inference('clc', [status(thm)], ['125', '126'])).
% 0.39/0.62  thf('157', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('158', plain,
% 0.39/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.62         ((v2_struct_0 @ X16)
% 0.39/0.62          | ~ (l1_struct_0 @ X16)
% 0.39/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.39/0.62              != (k2_struct_0 @ X16))
% 0.39/0.62          | ~ (v2_funct_1 @ X18)
% 0.39/0.62          | ((k1_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.39/0.62              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.39/0.62              = (k2_struct_0 @ X16))
% 0.39/0.62          | ~ (m1_subset_1 @ X18 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.39/0.62          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.39/0.62          | ~ (v1_funct_1 @ X18)
% 0.39/0.62          | ~ (l1_struct_0 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.39/0.62  thf('159', plain,
% 0.39/0.62      ((~ (l1_struct_0 @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.39/0.62            = (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62            != (k2_struct_0 @ sk_B))
% 0.39/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.62        | (v2_struct_0 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['157', '158'])).
% 0.39/0.62  thf('160', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.62      inference('sup-', [status(thm)], ['115', '116'])).
% 0.39/0.62  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('162', plain,
% 0.39/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('163', plain,
% 0.39/0.62      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.62  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '10', '11', '12', '13', '14'])).
% 0.39/0.62  thf('165', plain,
% 0.39/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.62         = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.39/0.62  thf('166', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('167', plain,
% 0.39/0.62      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.39/0.62        | (v2_struct_0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['159', '160', '161', '162', '163', '164', '165', '166'])).
% 0.39/0.62  thf('168', plain,
% 0.39/0.62      (((v2_struct_0 @ sk_B)
% 0.39/0.62        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['167'])).
% 0.39/0.62  thf('169', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('170', plain,
% 0.39/0.62      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.62         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.39/0.62      inference('clc', [status(thm)], ['168', '169'])).
% 0.39/0.62  thf('171', plain,
% 0.39/0.62      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.39/0.62        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.39/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['93', '145', '154', '155', '156', '170'])).
% 0.39/0.62  thf('172', plain, ((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.39/0.62      inference('simplify', [status(thm)], ['171'])).
% 0.39/0.62  thf('173', plain, ($false), inference('demod', [status(thm)], ['33', '172'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
