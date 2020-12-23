%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MI3LNTAFma

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:30 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  185 (1491 expanded)
%              Number of leaves         :   32 ( 465 expanded)
%              Depth                    :   19
%              Number of atoms          : 1961 (33915 expanded)
%              Number of equality atoms :   85 ( 452 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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

thf('7',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
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

thf('9',plain,(
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

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15'])).

thf('17',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ( v2_funct_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('27',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
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

thf('44',plain,
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
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 ) @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('61',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['56','57','58','59','60','61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','53','63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X13 @ X14 @ X15 ) @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('72',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('75',plain,(
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

thf('76',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('79',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('88',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','88'])).

thf('90',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('91',plain,(
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

thf('92',plain,(
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

thf('93',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('103',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','96','97','98','99','100','101','102'])).

thf('104',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
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

thf('106',plain,(
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

thf('107',plain,
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
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('113',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('115',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108','109','110','111','112','113','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','104','118'])).

thf('120',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['73','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('122',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v3_tops_2 @ X11 @ X12 @ X10 )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['126','127','128','129','130','131'])).

thf('133',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('134',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
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

thf('137',plain,
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
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21','22','23','24','25'])).

thf('143',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15'])).

thf('144',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','72','123','132','133','134','148'])).

thf('150',plain,(
    v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['34','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MI3LNTAFma
% 0.16/0.38  % Computer   : n019.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:33:38 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 412 iterations in 0.160s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.46/0.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.66  thf(t70_tops_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                 ( m1_subset_1 @
% 0.46/0.66                   C @ 
% 0.46/0.66                   ( k1_zfmisc_1 @
% 0.46/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.46/0.66                 ( v3_tops_2 @
% 0.46/0.66                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.46/0.66                   B @ A ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( l1_pre_topc @ A ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                    ( v1_funct_2 @
% 0.46/0.66                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                    ( m1_subset_1 @
% 0.46/0.66                      C @ 
% 0.46/0.66                      ( k1_zfmisc_1 @
% 0.46/0.66                        ( k2_zfmisc_1 @
% 0.46/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.46/0.66                    ( v3_tops_2 @
% 0.46/0.66                      ( k2_tops_2 @
% 0.46/0.66                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.46/0.66                      B @ A ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (~ (v3_tops_2 @ 
% 0.46/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.66          sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d3_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X5 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d4_tops_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.66         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X8 @ X7 @ X9) != (X7))
% 0.46/0.66          | ~ (v2_funct_1 @ X9)
% 0.46/0.66          | ((k2_tops_2 @ X8 @ X7 @ X9) = (k2_funct_1 @ X9))
% 0.46/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.46/0.66          | ~ (v1_funct_2 @ X9 @ X8 @ X7)
% 0.46/0.66          | ~ (v1_funct_1 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(d5_tops_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( l1_pre_topc @ B ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                 ( m1_subset_1 @
% 0.46/0.66                   C @ 
% 0.46/0.66                   ( k1_zfmisc_1 @
% 0.46/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.46/0.66                 ( ( ( k1_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                     ( k2_struct_0 @ A ) ) & 
% 0.46/0.66                   ( ( k2_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.66                   ( v5_pre_topc @
% 0.46/0.66                     ( k2_tops_2 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.46/0.66                     B @ A ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X10)
% 0.46/0.66          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.46/0.66          | ((k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11)
% 0.46/0.66              = (k2_struct_0 @ X10))
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.46/0.66          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.46/0.66          | ~ (v1_funct_1 @ X11)
% 0.46/0.66          | ~ (l1_pre_topc @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            = (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('14', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11', '12', '13', '14', '15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['7', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X10)
% 0.46/0.66          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.46/0.66          | (v2_funct_1 @ X11)
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.46/0.66          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.46/0.66          | ~ (v1_funct_1 @ X11)
% 0.46/0.66          | ~ (l1_pre_topc @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v2_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.66  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('24', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('26', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['17', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            = (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '27'])).
% 0.46/0.66  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_l1_pre_topc, axiom,
% 0.46/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.66  thf('30', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.66  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            = (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['28', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('34', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_k2_tops_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.46/0.66         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.46/0.66         ( m1_subset_1 @
% 0.46/0.66           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.46/0.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (k2_tops_2 @ X13 @ X14 @ X15) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.46/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.46/0.66          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.46/0.66          | ~ (v1_funct_1 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (m1_subset_1 @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((m1_subset_1 @ 
% 0.46/0.66        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X10)
% 0.46/0.66          | ((k1_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11)
% 0.46/0.66              != (k2_struct_0 @ X12))
% 0.46/0.66          | ((k2_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11)
% 0.46/0.66              != (k2_struct_0 @ X10))
% 0.46/0.66          | ~ (v2_funct_1 @ X11)
% 0.46/0.66          | ~ (v5_pre_topc @ X11 @ X12 @ X10)
% 0.46/0.66          | ~ (v5_pre_topc @ 
% 0.46/0.66               (k2_tops_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11) @ 
% 0.46/0.66               X10 @ X12)
% 0.46/0.66          | (v3_tops_2 @ X11 @ X12 @ X10)
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.46/0.66          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.46/0.66          | ~ (v1_funct_1 @ X11)
% 0.46/0.66          | ~ (l1_pre_topc @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66             (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.66        | ~ (v5_pre_topc @ 
% 0.46/0.66             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66             sk_A @ sk_B)
% 0.46/0.66        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_tops_2 @ X13 @ X14 @ X15))
% 0.46/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.46/0.66          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.46/0.66          | ~ (v1_funct_1 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v1_funct_1 @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      ((v1_funct_1 @ 
% 0.46/0.66        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X10)
% 0.46/0.66          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.46/0.66          | (v5_pre_topc @ 
% 0.46/0.66             (k2_tops_2 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11) @ 
% 0.46/0.66             X10 @ X12)
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.46/0.66          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.46/0.66          | ~ (v1_funct_1 @ X11)
% 0.46/0.66          | ~ (l1_pre_topc @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v5_pre_topc @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.66           sk_B @ sk_A)
% 0.46/0.66        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.66  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('61', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('63', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['56', '57', '58', '59', '60', '61', '62'])).
% 0.46/0.66  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66           (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.66        | ~ (v5_pre_topc @ 
% 0.46/0.66             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66             sk_A @ sk_B)
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['44', '45', '53', '63', '64'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((v1_funct_2 @ (k2_tops_2 @ X13 @ X14 @ X15) @ X14 @ X13)
% 0.46/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.46/0.66          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.46/0.66          | ~ (v1_funct_1 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v1_funct_2 @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.66           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X5 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X8 @ X7 @ X9) != (X7))
% 0.46/0.66          | ~ (v2_funct_1 @ X9)
% 0.46/0.66          | ((k2_tops_2 @ X8 @ X7 @ X9) = (k2_funct_1 @ X9))
% 0.46/0.66          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X7)))
% 0.46/0.66          | ~ (v1_funct_2 @ X9 @ X8 @ X7)
% 0.46/0.66          | ~ (v1_funct_1 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66             (u1_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.66  thf('77', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t65_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X4 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X4)
% 0.46/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.46/0.66          | ~ (v1_funct_1 @ X4)
% 0.46/0.66          | ~ (v1_relat_1 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc2_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.66          | (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ 
% 0.46/0.66           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | (v1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.66  thf(fc6_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.66  thf('84', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.66  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)) | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['80', '85'])).
% 0.46/0.66  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.46/0.66  thf('88', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66           (u1_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['76', '77', '88'])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t63_tops_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( l1_struct_0 @ B ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                 ( m1_subset_1 @
% 0.46/0.66                   C @ 
% 0.46/0.66                   ( k1_zfmisc_1 @
% 0.46/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66               ( ( ( ( k2_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.66                 ( v2_funct_1 @
% 0.46/0.66                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.66         (~ (l1_struct_0 @ X19)
% 0.46/0.66          | ((k2_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21)
% 0.46/0.66              != (k2_struct_0 @ X19))
% 0.46/0.66          | ~ (v2_funct_1 @ X21)
% 0.46/0.66          | (v2_funct_1 @ 
% 0.46/0.66             (k2_tops_2 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21))
% 0.46/0.66          | ~ (m1_subset_1 @ X21 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.46/0.66          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.46/0.66          | ~ (v1_funct_1 @ X21)
% 0.46/0.66          | ~ (l1_struct_0 @ X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v2_funct_1 @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.66  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('95', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.66  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.66  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('98', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11', '12', '13', '14', '15'])).
% 0.46/0.66  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['93', '96', '97', '98', '99', '100', '101', '102'])).
% 0.46/0.66  thf('104', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['103'])).
% 0.46/0.66  thf('105', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t62_tops_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                 ( m1_subset_1 @
% 0.46/0.66                   C @ 
% 0.46/0.66                   ( k1_zfmisc_1 @
% 0.46/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66               ( ( ( ( k2_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.66                 ( ( ( k1_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                       ( k2_tops_2 @
% 0.46/0.66                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                   ( ( k2_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                       ( k2_tops_2 @
% 0.46/0.66                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.66                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('106', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.66         ((v2_struct_0 @ X16)
% 0.46/0.66          | ~ (l1_struct_0 @ X16)
% 0.46/0.66          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.46/0.66              != (k2_struct_0 @ X16))
% 0.46/0.66          | ~ (v2_funct_1 @ X18)
% 0.46/0.66          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.46/0.66              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.46/0.66              = (k2_struct_0 @ X17))
% 0.46/0.66          | ~ (m1_subset_1 @ X18 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.46/0.66          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X18)
% 0.46/0.66          | ~ (l1_struct_0 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.46/0.66  thf('107', plain,
% 0.46/0.66      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.66            = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.66        | (v2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['105', '106'])).
% 0.46/0.66  thf('108', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.66  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.46/0.66  thf('113', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11', '12', '13', '14', '15'])).
% 0.46/0.66  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['107', '108', '109', '110', '111', '112', '113', '114'])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_B)
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['115'])).
% 0.46/0.66  thf('117', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('118', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['116', '117'])).
% 0.46/0.66  thf('119', plain,
% 0.46/0.66      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['89', '90', '104', '118'])).
% 0.46/0.66  thf('120', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['73', '119'])).
% 0.46/0.66  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.66  thf('122', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['120', '121'])).
% 0.46/0.66  thf('123', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['122'])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('125', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X10)
% 0.46/0.66          | ~ (v3_tops_2 @ X11 @ X12 @ X10)
% 0.46/0.66          | (v5_pre_topc @ X11 @ X12 @ X10)
% 0.46/0.66          | ~ (m1_subset_1 @ X11 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 0.46/0.66          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 0.46/0.66          | ~ (v1_funct_1 @ X11)
% 0.46/0.66          | ~ (l1_pre_topc @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.66  thf('126', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.46/0.66        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['124', '125'])).
% 0.46/0.66  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('129', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('130', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('132', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['126', '127', '128', '129', '130', '131'])).
% 0.46/0.66  thf('133', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['103'])).
% 0.46/0.66  thf('134', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['116', '117'])).
% 0.46/0.66  thf('135', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('136', plain,
% 0.46/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.66         ((v2_struct_0 @ X16)
% 0.46/0.66          | ~ (l1_struct_0 @ X16)
% 0.46/0.66          | ((k2_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18)
% 0.46/0.66              != (k2_struct_0 @ X16))
% 0.46/0.66          | ~ (v2_funct_1 @ X18)
% 0.46/0.66          | ((k1_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.46/0.66              (k2_tops_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18))
% 0.46/0.66              = (k2_struct_0 @ X16))
% 0.46/0.66          | ~ (m1_subset_1 @ X18 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))))
% 0.46/0.66          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.46/0.66          | ~ (v1_funct_1 @ X18)
% 0.46/0.66          | ~ (l1_struct_0 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.46/0.66  thf('137', plain,
% 0.46/0.66      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.66            = (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.66        | (v2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['135', '136'])).
% 0.46/0.66  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.66  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('140', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('141', plain,
% 0.46/0.66      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.66  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '21', '22', '23', '24', '25'])).
% 0.46/0.66  thf('143', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11', '12', '13', '14', '15'])).
% 0.46/0.66  thf('144', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('145', plain,
% 0.46/0.66      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['137', '138', '139', '140', '141', '142', '143', '144'])).
% 0.46/0.66  thf('146', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_B)
% 0.46/0.66        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['145'])).
% 0.46/0.66  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('148', plain,
% 0.46/0.66      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['146', '147'])).
% 0.46/0.66  thf('149', plain,
% 0.46/0.66      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.66        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['65', '72', '123', '132', '133', '134', '148'])).
% 0.46/0.66  thf('150', plain, ((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.46/0.66      inference('simplify', [status(thm)], ['149'])).
% 0.46/0.66  thf('151', plain, ($false), inference('demod', [status(thm)], ['34', '150'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
