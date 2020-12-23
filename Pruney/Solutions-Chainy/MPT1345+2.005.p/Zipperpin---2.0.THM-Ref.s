%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e4l1XSvDfB

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  293 (3043 expanded)
%              Number of leaves         :   31 ( 941 expanded)
%              Depth                    :   25
%              Number of atoms          : 3196 (67912 expanded)
%              Number of equality atoms :  157 ( 811 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X9 @ X11 )
       != X9 )
      | ~ ( v2_funct_1 @ X11 )
      | ( ( k2_tops_2 @ X10 @ X9 @ X11 )
        = ( k2_funct_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tops_2 @ X13 @ X14 @ X12 )
      | ( v2_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('29',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','19','28'])).

thf('30',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tops_2 @ X13 @ X14 @ X12 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 )
        = ( k2_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('40',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('42',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','42'])).

thf('44',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relset_1 @ X6 @ X5 @ X4 )
       != X5 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 )
       != ( k2_struct_0 @ X14 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 )
       != ( k2_struct_0 @ X12 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v5_pre_topc @ X13 @ X14 @ X12 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 ) @ X12 @ X14 )
      | ( v3_tops_2 @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v3_tops_2 @ X2 @ X0 @ X1 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 ) @ X1 @ X0 )
      | ~ ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 )
       != ( k2_struct_0 @ X1 ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tops_2 @ X13 @ X14 @ X12 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) @ X13 ) @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['64','65','66','67','68','69'])).

thf('71',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('73',plain,(
    v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['43'])).

thf('75',plain,(
    v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relset_1 @ X6 @ X5 @ X4 )
       != X5 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X4 ) @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('83',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('88',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relset_1 @ X6 @ X5 @ X4 )
       != X5 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('98',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('100',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('103',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('107',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','75','89','104','105','106'])).

thf('108',plain,(
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

thf('109',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X15 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) @ X17 )
       != ( k2_struct_0 @ X15 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) @ X17 ) )
        = ( k2_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('110',plain,
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
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('119',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['110','113','114','115','116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X9 @ X11 )
       != X9 )
      | ~ ( v2_funct_1 @ X11 )
      | ( ( k2_tops_2 @ X10 @ X9 @ X11 )
        = ( k2_funct_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('128',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('130',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('133',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X15 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) @ X17 )
       != ( k2_struct_0 @ X15 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) @ X17 ) )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('140',plain,
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
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('147',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('148',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141','142','143','144','145','146','147'])).

thf('149',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
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

thf('153',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) @ X20 )
       != ( k2_struct_0 @ X18 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('154',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('160',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('161',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('162',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158','159','160','161'])).

thf('163',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relset_1 @ X6 @ X5 @ X4 )
       != X5 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('168',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('172',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38'])).

thf('174',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['165','174'])).

thf('176',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('177',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X9 @ X11 )
       != X9 )
      | ~ ( v2_funct_1 @ X11 )
      | ( ( k2_tops_2 @ X10 @ X9 @ X11 )
        = ( k2_funct_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('180',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('182',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('183',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('185',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('186',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['164','186'])).

thf('188',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('189',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('192',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('194',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relset_1 @ X6 @ X5 @ X4 )
       != X5 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('195',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('197',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('198',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('199',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('201',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','201'])).

thf('203',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('204',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('205',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('207',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('209',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['202','207','208'])).

thf('210',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['192','209'])).

thf('211',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('212',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('215',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tops_2 @ X13 @ X14 @ X12 )
      | ( v5_pre_topc @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ X2 @ X1 @ X0 )
      | ~ ( v3_tops_2 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['213','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('220',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('221',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relset_1 @ X6 @ X5 @ X4 )
       != X5 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X4 ) @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('222',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('224',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('225',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('227',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('228',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','228'])).

thf('230',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('231',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('234',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('235',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relset_1 @ X6 @ X5 @ X4 )
       != X5 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X4 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('236',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('238',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['88'])).

thf('239',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('241',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('242',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['233','242'])).

thf('244',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('245',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('249',plain,
    ( ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['217','218','232','246','247','248'])).

thf('250',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['191','249'])).

thf('251',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('253',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('254',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['22','23','24','25','26','27'])).

thf('257',plain,(
    v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['250','251','254','255','256'])).

thf('258',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','137','151','163','190','257'])).

thf('259',plain,(
    v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,(
    $false ),
    inference(demod,[status(thm)],['45','259'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e4l1XSvDfB
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 277 iterations in 0.117s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.59  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.21/0.59  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.21/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.59  thf(d3_struct_0, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (![X7 : $i]:
% 0.21/0.59         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.59  thf(t70_tops_2, conjecture,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( l1_pre_topc @ A ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.59           ( ![C:$i]:
% 0.21/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.59                 ( m1_subset_1 @
% 0.21/0.59                   C @ 
% 0.21/0.59                   ( k1_zfmisc_1 @
% 0.21/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.59               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.21/0.59                 ( v3_tops_2 @
% 0.21/0.59                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.21/0.59                   B @ A ) ) ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i]:
% 0.21/0.59        ( ( l1_pre_topc @ A ) =>
% 0.21/0.59          ( ![B:$i]:
% 0.21/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.59              ( ![C:$i]:
% 0.21/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.59                    ( v1_funct_2 @
% 0.21/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.59                    ( m1_subset_1 @
% 0.21/0.59                      C @ 
% 0.21/0.59                      ( k1_zfmisc_1 @
% 0.21/0.59                        ( k2_zfmisc_1 @
% 0.21/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.59                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.21/0.59                    ( v3_tops_2 @
% 0.21/0.59                      ( k2_tops_2 @
% 0.21/0.59                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.21/0.59                      B @ A ) ) ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      (~ (v3_tops_2 @ 
% 0.21/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.59          sk_B @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      ((~ (v3_tops_2 @ 
% 0.21/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.59           sk_B @ sk_A)
% 0.21/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.59  thf('3', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(dt_l1_pre_topc, axiom,
% 0.21/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.59  thf('4', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.59  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (~ (v3_tops_2 @ 
% 0.21/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.59          sk_B @ sk_A)),
% 0.21/0.59      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X7 : $i]:
% 0.21/0.59         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_C @ 
% 0.21/0.59        (k1_zfmisc_1 @ 
% 0.21/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (((m1_subset_1 @ sk_C @ 
% 0.21/0.59         (k1_zfmisc_1 @ 
% 0.21/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.59  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_C @ 
% 0.21/0.59        (k1_zfmisc_1 @ 
% 0.21/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.59  thf(d4_tops_2, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.59       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.59         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.59         (((k2_relset_1 @ X10 @ X9 @ X11) != (X9))
% 0.21/0.59          | ~ (v2_funct_1 @ X11)
% 0.21/0.59          | ((k2_tops_2 @ X10 @ X9 @ X11) = (k2_funct_1 @ X11))
% 0.21/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.21/0.59          | ~ (v1_funct_2 @ X11 @ X10 @ X9)
% 0.21/0.59          | ~ (v1_funct_1 @ X11))),
% 0.21/0.59      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.59        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.59            = (k2_funct_1 @ sk_C))
% 0.21/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.59            != (k2_struct_0 @ sk_B)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.59  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      (![X7 : $i]:
% 0.21/0.59         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.59  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_C @ 
% 0.21/0.59        (k1_zfmisc_1 @ 
% 0.21/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(d5_tops_2, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( l1_pre_topc @ A ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( l1_pre_topc @ B ) =>
% 0.21/0.59           ( ![C:$i]:
% 0.21/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.59                 ( m1_subset_1 @
% 0.21/0.59                   C @ 
% 0.21/0.59                   ( k1_zfmisc_1 @
% 0.21/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.59               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.21/0.59                 ( ( ( k1_relset_1 @
% 0.21/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.59                     ( k2_struct_0 @ A ) ) & 
% 0.21/0.59                   ( ( k2_relset_1 @
% 0.21/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.59                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.59                   ( v5_pre_topc @
% 0.21/0.59                     ( k2_tops_2 @
% 0.21/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.21/0.59                     B @ A ) ) ) ) ) ) ) ))).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         (~ (l1_pre_topc @ X12)
% 0.21/0.59          | ~ (v3_tops_2 @ X13 @ X14 @ X12)
% 0.21/0.59          | (v2_funct_1 @ X13)
% 0.21/0.59          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.59               (k1_zfmisc_1 @ 
% 0.21/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.21/0.59          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.21/0.59          | ~ (v1_funct_1 @ X13)
% 0.21/0.59          | ~ (l1_pre_topc @ X14))),
% 0.21/0.59      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.59  thf('22', plain,
% 0.21/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.59        | (v2_funct_1 @ sk_C)
% 0.21/0.59        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.59  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('26', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('28', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.59      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.21/0.59  thf('29', plain,
% 0.21/0.59      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.59          = (k2_funct_1 @ sk_C))
% 0.21/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.59            != (k2_struct_0 @ sk_B)))),
% 0.21/0.59      inference('demod', [status(thm)], ['13', '14', '19', '28'])).
% 0.21/0.59  thf('30', plain,
% 0.21/0.59      (![X7 : $i]:
% 0.21/0.59         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      ((m1_subset_1 @ sk_C @ 
% 0.21/0.59        (k1_zfmisc_1 @ 
% 0.21/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         (~ (l1_pre_topc @ X12)
% 0.21/0.59          | ~ (v3_tops_2 @ X13 @ X14 @ X12)
% 0.21/0.59          | ((k2_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ X13)
% 0.21/0.59              = (k2_struct_0 @ X12))
% 0.21/0.59          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.59               (k1_zfmisc_1 @ 
% 0.21/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.21/0.59          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.21/0.59          | ~ (v1_funct_1 @ X13)
% 0.21/0.59          | ~ (l1_pre_topc @ X14))),
% 0.21/0.59      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.59  thf('33', plain,
% 0.21/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.59        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.59            = (k2_struct_0 @ sk_B))
% 0.21/0.59        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.59        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.59  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('37', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60         = (k2_struct_0 @ sk_B))),
% 0.21/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60          = (k2_struct_0 @ sk_B))
% 0.21/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.60      inference('sup+', [status(thm)], ['30', '39'])).
% 0.21/0.60  thf('41', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.60  thf('42', plain,
% 0.21/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60         = (k2_struct_0 @ sk_B))),
% 0.21/0.60      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60          = (k2_funct_1 @ sk_C))
% 0.21/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['29', '42'])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60         = (k2_funct_1 @ sk_C))),
% 0.21/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.60  thf('45', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.21/0.60      inference('demod', [status(thm)], ['6', '44'])).
% 0.21/0.60  thf('46', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C @ 
% 0.21/0.60        (k1_zfmisc_1 @ 
% 0.21/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.60  thf(t31_funct_2, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.60       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.60         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.60           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.60           ( m1_subset_1 @
% 0.21/0.60             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.60         (~ (v2_funct_1 @ X4)
% 0.21/0.60          | ((k2_relset_1 @ X6 @ X5 @ X4) != (X5))
% 0.21/0.60          | (m1_subset_1 @ (k2_funct_1 @ X4) @ 
% 0.21/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.21/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.21/0.60          | ~ (v1_funct_2 @ X4 @ X6 @ X5)
% 0.21/0.60          | ~ (v1_funct_1 @ X4))),
% 0.21/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.21/0.60  thf('48', plain,
% 0.21/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.60        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.60           (k1_zfmisc_1 @ 
% 0.21/0.60            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60            != (k2_struct_0 @ sk_B))
% 0.21/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.60  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('50', plain,
% 0.21/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.60  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.21/0.60  thf('52', plain,
% 0.21/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.60         (k1_zfmisc_1 @ 
% 0.21/0.60          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60            != (k2_struct_0 @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.21/0.60  thf('53', plain,
% 0.21/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60         = (k2_struct_0 @ sk_B))),
% 0.21/0.60      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.60  thf('54', plain,
% 0.21/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.60         (k1_zfmisc_1 @ 
% 0.21/0.60          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.60  thf('55', plain,
% 0.21/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.60        (k1_zfmisc_1 @ 
% 0.21/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.60      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.60  thf('56', plain,
% 0.21/0.60      (![X7 : $i]:
% 0.21/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.60  thf('57', plain,
% 0.21/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.60         (~ (l1_pre_topc @ X12)
% 0.21/0.60          | ((k1_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ X13)
% 0.21/0.60              != (k2_struct_0 @ X14))
% 0.21/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ X13)
% 0.21/0.60              != (k2_struct_0 @ X12))
% 0.21/0.60          | ~ (v2_funct_1 @ X13)
% 0.21/0.60          | ~ (v5_pre_topc @ X13 @ X14 @ X12)
% 0.21/0.60          | ~ (v5_pre_topc @ 
% 0.21/0.60               (k2_tops_2 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ X13) @ 
% 0.21/0.60               X12 @ X14)
% 0.21/0.60          | (v3_tops_2 @ X13 @ X14 @ X12)
% 0.21/0.60          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.60               (k1_zfmisc_1 @ 
% 0.21/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.21/0.60          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.21/0.60          | ~ (v1_funct_1 @ X13)
% 0.21/0.60          | ~ (l1_pre_topc @ X14))),
% 0.21/0.60      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.60  thf('58', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X2 @ 
% 0.21/0.60             (k1_zfmisc_1 @ 
% 0.21/0.60              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.21/0.60          | ~ (l1_struct_0 @ X0)
% 0.21/0.60          | ~ (l1_pre_topc @ X0)
% 0.21/0.60          | ~ (v1_funct_1 @ X2)
% 0.21/0.60          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.21/0.60          | (v3_tops_2 @ X2 @ X0 @ X1)
% 0.21/0.60          | ~ (v5_pre_topc @ 
% 0.21/0.60               (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2) @ 
% 0.21/0.60               X1 @ X0)
% 0.21/0.60          | ~ (v5_pre_topc @ X2 @ X0 @ X1)
% 0.21/0.60          | ~ (v2_funct_1 @ X2)
% 0.21/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2)
% 0.21/0.60              != (k2_struct_0 @ X1))
% 0.21/0.60          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2)
% 0.21/0.60              != (k2_struct_0 @ X0))
% 0.21/0.60          | ~ (l1_pre_topc @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.60  thf('59', plain,
% 0.21/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.60        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.21/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.60        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.60        | ~ (v5_pre_topc @ 
% 0.21/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60              (k2_funct_1 @ sk_C)) @ 
% 0.21/0.60             sk_A @ sk_B)
% 0.21/0.60        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.21/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.60             (u1_struct_0 @ sk_A))
% 0.21/0.60        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.60        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.60      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.60  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('61', plain,
% 0.21/0.60      (![X7 : $i]:
% 0.21/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.60  thf('62', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C @ 
% 0.21/0.60        (k1_zfmisc_1 @ 
% 0.21/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('63', plain,
% 0.21/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.60         (~ (l1_pre_topc @ X12)
% 0.21/0.60          | ~ (v3_tops_2 @ X13 @ X14 @ X12)
% 0.21/0.60          | (v5_pre_topc @ 
% 0.21/0.60             (k2_tops_2 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12) @ X13) @ 
% 0.21/0.60             X12 @ X14)
% 0.21/0.60          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.60               (k1_zfmisc_1 @ 
% 0.21/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.21/0.60          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.21/0.60          | ~ (v1_funct_1 @ X13)
% 0.21/0.60          | ~ (l1_pre_topc @ X14))),
% 0.21/0.60      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.21/0.60  thf('64', plain,
% 0.21/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.60        | (v5_pre_topc @ 
% 0.21/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.60           sk_B @ sk_A)
% 0.21/0.60        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.60        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.60  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('67', plain,
% 0.21/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('68', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('70', plain,
% 0.21/0.60      ((v5_pre_topc @ 
% 0.21/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.60        sk_B @ sk_A)),
% 0.21/0.60      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '69'])).
% 0.21/0.60  thf('71', plain,
% 0.21/0.60      (((v5_pre_topc @ 
% 0.21/0.60         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.60         sk_B @ sk_A)
% 0.21/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.60      inference('sup+', [status(thm)], ['61', '70'])).
% 0.21/0.60  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.60  thf('73', plain,
% 0.21/0.60      ((v5_pre_topc @ 
% 0.21/0.60        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.21/0.60        sk_B @ sk_A)),
% 0.21/0.60      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.60  thf('74', plain,
% 0.21/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60         = (k2_funct_1 @ sk_C))),
% 0.21/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.60  thf('75', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.21/0.60      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.60  thf('76', plain,
% 0.21/0.60      (![X7 : $i]:
% 0.21/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.60  thf('77', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C @ 
% 0.21/0.60        (k1_zfmisc_1 @ 
% 0.21/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('78', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.60         (~ (v2_funct_1 @ X4)
% 0.21/0.60          | ((k2_relset_1 @ X6 @ X5 @ X4) != (X5))
% 0.21/0.60          | (v1_funct_2 @ (k2_funct_1 @ X4) @ X5 @ X6)
% 0.21/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.21/0.60          | ~ (v1_funct_2 @ X4 @ X6 @ X5)
% 0.21/0.60          | ~ (v1_funct_1 @ X4))),
% 0.21/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.21/0.60  thf('79', plain,
% 0.21/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.60        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.60           (u1_struct_0 @ sk_A))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60            != (u1_struct_0 @ sk_B))
% 0.21/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.60      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.60  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('81', plain,
% 0.21/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.21/0.60  thf('83', plain,
% 0.21/0.60      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.60         (u1_struct_0 @ sk_A))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60            != (u1_struct_0 @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.21/0.60  thf('84', plain,
% 0.21/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60         = (k2_struct_0 @ sk_B))),
% 0.21/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.21/0.60  thf('85', plain,
% 0.21/0.60      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.60         (u1_struct_0 @ sk_A))
% 0.21/0.60        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['83', '84'])).
% 0.21/0.60  thf('86', plain,
% 0.21/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.60        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.60           (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['76', '85'])).
% 0.21/0.60  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.60  thf('88', plain,
% 0.21/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.60        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.60           (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.60  thf('89', plain,
% 0.21/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.60        (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.60  thf('90', plain,
% 0.21/0.60      (![X7 : $i]:
% 0.21/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.60  thf('91', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C @ 
% 0.21/0.60        (k1_zfmisc_1 @ 
% 0.21/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('92', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.60         (~ (v2_funct_1 @ X4)
% 0.21/0.60          | ((k2_relset_1 @ X6 @ X5 @ X4) != (X5))
% 0.21/0.60          | (v1_funct_1 @ (k2_funct_1 @ X4))
% 0.21/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.21/0.60          | ~ (v1_funct_2 @ X4 @ X6 @ X5)
% 0.21/0.60          | ~ (v1_funct_1 @ X4))),
% 0.21/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.21/0.60  thf('93', plain,
% 0.21/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.60        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60            != (u1_struct_0 @ sk_B))
% 0.21/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.60      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.60  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('95', plain,
% 0.21/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('96', plain,
% 0.21/0.60      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60            != (u1_struct_0 @ sk_B))
% 0.21/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.60      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.21/0.60  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.21/0.60  thf('98', plain,
% 0.21/0.60      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60            != (u1_struct_0 @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.60  thf('99', plain,
% 0.21/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.60         = (k2_struct_0 @ sk_B))),
% 0.21/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.21/0.60  thf('100', plain,
% 0.21/0.60      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.60        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.21/0.60      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.60  thf('101', plain,
% 0.21/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.60        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['90', '100'])).
% 0.21/0.60  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.60  thf('103', plain,
% 0.21/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.60        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.60      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.60  thf('104', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.21/0.60      inference('simplify', [status(thm)], ['103'])).
% 0.21/0.60  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.60  thf('107', plain,
% 0.21/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.21/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.21/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.60        | ~ (v5_pre_topc @ 
% 0.21/0.60             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.60              (k2_funct_1 @ sk_C)) @ 
% 0.21/0.60             sk_A @ sk_B)
% 0.21/0.60        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.21/0.60      inference('demod', [status(thm)],
% 0.21/0.60                ['59', '60', '75', '89', '104', '105', '106'])).
% 0.21/0.60  thf('108', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C @ 
% 0.21/0.60        (k1_zfmisc_1 @ 
% 0.21/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t62_tops_2, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( l1_struct_0 @ A ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.60           ( ![C:$i]:
% 0.21/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.60                 ( m1_subset_1 @
% 0.43/0.60                   C @ 
% 0.43/0.60                   ( k1_zfmisc_1 @
% 0.43/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.43/0.60               ( ( ( ( k2_relset_1 @
% 0.43/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.43/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.43/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.43/0.60                 ( ( ( k1_relset_1 @
% 0.43/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.43/0.60                       ( k2_tops_2 @
% 0.43/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.43/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.43/0.60                   ( ( k2_relset_1 @
% 0.43/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.43/0.60                       ( k2_tops_2 @
% 0.43/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.43/0.60                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.43/0.60  thf('109', plain,
% 0.43/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.60         ((v2_struct_0 @ X15)
% 0.43/0.60          | ~ (l1_struct_0 @ X15)
% 0.43/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17)
% 0.43/0.60              != (k2_struct_0 @ X15))
% 0.43/0.60          | ~ (v2_funct_1 @ X17)
% 0.43/0.60          | ((k1_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16) @ 
% 0.43/0.60              (k2_tops_2 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17))
% 0.43/0.60              = (k2_struct_0 @ X15))
% 0.43/0.60          | ~ (m1_subset_1 @ X17 @ 
% 0.43/0.60               (k1_zfmisc_1 @ 
% 0.43/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))))
% 0.43/0.60          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.43/0.60          | ~ (v1_funct_1 @ X17)
% 0.43/0.60          | ~ (l1_struct_0 @ X16))),
% 0.43/0.60      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.43/0.60  thf('110', plain,
% 0.43/0.60      ((~ (l1_struct_0 @ sk_A)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.43/0.60            = (k2_struct_0 @ sk_B))
% 0.43/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            != (k2_struct_0 @ sk_B))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.43/0.60        | (v2_struct_0 @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['108', '109'])).
% 0.43/0.60  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('112', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.43/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.60  thf('113', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.60  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('115', plain,
% 0.43/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.43/0.60  thf('117', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_struct_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.43/0.60  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('119', plain,
% 0.43/0.60      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.43/0.60          = (k2_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.43/0.60        | (v2_struct_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)],
% 0.43/0.60                ['110', '113', '114', '115', '116', '117', '118'])).
% 0.43/0.60  thf('120', plain,
% 0.43/0.60      (((v2_struct_0 @ sk_B)
% 0.43/0.60        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.43/0.60            = (k2_struct_0 @ sk_B)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['119'])).
% 0.43/0.60  thf('121', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('122', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('123', plain,
% 0.43/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.60         (((k2_relset_1 @ X10 @ X9 @ X11) != (X9))
% 0.43/0.60          | ~ (v2_funct_1 @ X11)
% 0.43/0.60          | ((k2_tops_2 @ X10 @ X9 @ X11) = (k2_funct_1 @ X11))
% 0.43/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.43/0.60          | ~ (v1_funct_2 @ X11 @ X10 @ X9)
% 0.43/0.60          | ~ (v1_funct_1 @ X11))),
% 0.43/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.43/0.60  thf('124', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            = (k2_funct_1 @ sk_C))
% 0.43/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            != (u1_struct_0 @ sk_B)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['122', '123'])).
% 0.43/0.60  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('126', plain,
% 0.43/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.43/0.60  thf('128', plain,
% 0.43/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60          = (k2_funct_1 @ sk_C))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            != (u1_struct_0 @ sk_B)))),
% 0.43/0.60      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.43/0.60  thf('129', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_struct_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.43/0.60  thf('130', plain,
% 0.43/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60          = (k2_funct_1 @ sk_C))
% 0.43/0.60        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.43/0.60      inference('demod', [status(thm)], ['128', '129'])).
% 0.43/0.60  thf('131', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.43/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            = (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['121', '130'])).
% 0.43/0.60  thf('132', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('133', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            = (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('demod', [status(thm)], ['131', '132'])).
% 0.43/0.60  thf('134', plain,
% 0.43/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['133'])).
% 0.43/0.60  thf('135', plain,
% 0.43/0.60      (((v2_struct_0 @ sk_B)
% 0.43/0.60        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.43/0.60      inference('demod', [status(thm)], ['120', '134'])).
% 0.43/0.60  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('137', plain,
% 0.43/0.60      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.43/0.60      inference('clc', [status(thm)], ['135', '136'])).
% 0.43/0.60  thf('138', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('139', plain,
% 0.43/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.60         ((v2_struct_0 @ X15)
% 0.43/0.60          | ~ (l1_struct_0 @ X15)
% 0.43/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17)
% 0.43/0.60              != (k2_struct_0 @ X15))
% 0.43/0.60          | ~ (v2_funct_1 @ X17)
% 0.43/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16) @ 
% 0.43/0.60              (k2_tops_2 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17))
% 0.43/0.60              = (k2_struct_0 @ X16))
% 0.43/0.60          | ~ (m1_subset_1 @ X17 @ 
% 0.43/0.60               (k1_zfmisc_1 @ 
% 0.43/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))))
% 0.43/0.60          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.43/0.60          | ~ (v1_funct_1 @ X17)
% 0.43/0.60          | ~ (l1_struct_0 @ X16))),
% 0.43/0.60      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.43/0.60  thf('140', plain,
% 0.43/0.60      ((~ (l1_struct_0 @ sk_A)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.43/0.60            = (k2_struct_0 @ sk_A))
% 0.43/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            != (k2_struct_0 @ sk_B))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.43/0.60        | (v2_struct_0 @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['138', '139'])).
% 0.43/0.60  thf('141', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.60  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('143', plain,
% 0.43/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('144', plain,
% 0.43/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['133'])).
% 0.43/0.60  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.43/0.60  thf('146', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_struct_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.43/0.60  thf('147', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('148', plain,
% 0.43/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.43/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.43/0.60        | (v2_struct_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)],
% 0.43/0.60                ['140', '141', '142', '143', '144', '145', '146', '147'])).
% 0.43/0.60  thf('149', plain,
% 0.43/0.60      (((v2_struct_0 @ sk_B)
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['148'])).
% 0.43/0.60  thf('150', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('151', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.43/0.60      inference('clc', [status(thm)], ['149', '150'])).
% 0.43/0.60  thf('152', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t63_tops_2, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ( l1_struct_0 @ A ) =>
% 0.43/0.60       ( ![B:$i]:
% 0.43/0.60         ( ( l1_struct_0 @ B ) =>
% 0.43/0.60           ( ![C:$i]:
% 0.43/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.60                 ( m1_subset_1 @
% 0.43/0.60                   C @ 
% 0.43/0.60                   ( k1_zfmisc_1 @
% 0.43/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.43/0.60               ( ( ( ( k2_relset_1 @
% 0.43/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.43/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.43/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.43/0.60                 ( v2_funct_1 @
% 0.43/0.60                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.43/0.60  thf('153', plain,
% 0.43/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.60         (~ (l1_struct_0 @ X18)
% 0.43/0.60          | ((k2_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20)
% 0.43/0.60              != (k2_struct_0 @ X18))
% 0.43/0.60          | ~ (v2_funct_1 @ X20)
% 0.43/0.60          | (v2_funct_1 @ 
% 0.43/0.60             (k2_tops_2 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20))
% 0.43/0.60          | ~ (m1_subset_1 @ X20 @ 
% 0.43/0.60               (k1_zfmisc_1 @ 
% 0.43/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.43/0.60          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.43/0.60          | ~ (v1_funct_1 @ X20)
% 0.43/0.60          | ~ (l1_struct_0 @ X19))),
% 0.43/0.60      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.43/0.60  thf('154', plain,
% 0.43/0.60      ((~ (l1_struct_0 @ sk_A)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | (v2_funct_1 @ 
% 0.43/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.43/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            != (k2_struct_0 @ sk_B))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['152', '153'])).
% 0.43/0.60  thf('155', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.60  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('157', plain,
% 0.43/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('158', plain,
% 0.43/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['133'])).
% 0.43/0.60  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.43/0.60  thf('160', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_struct_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.43/0.60  thf('161', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('162', plain,
% 0.43/0.60      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.43/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.43/0.60      inference('demod', [status(thm)],
% 0.43/0.60                ['154', '155', '156', '157', '158', '159', '160', '161'])).
% 0.43/0.60  thf('163', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['162'])).
% 0.43/0.60  thf('164', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('165', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('166', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('167', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (~ (v2_funct_1 @ X4)
% 0.43/0.60          | ((k2_relset_1 @ X6 @ X5 @ X4) != (X5))
% 0.43/0.60          | (m1_subset_1 @ (k2_funct_1 @ X4) @ 
% 0.43/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.43/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.43/0.60          | ~ (v1_funct_2 @ X4 @ X6 @ X5)
% 0.43/0.60          | ~ (v1_funct_1 @ X4))),
% 0.43/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.43/0.60  thf('168', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60           (k1_zfmisc_1 @ 
% 0.43/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            != (u1_struct_0 @ sk_B))
% 0.43/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.43/0.60      inference('sup-', [status(thm)], ['166', '167'])).
% 0.43/0.60  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('170', plain,
% 0.43/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.43/0.60  thf('172', plain,
% 0.43/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60         (k1_zfmisc_1 @ 
% 0.43/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60            != (u1_struct_0 @ sk_B)))),
% 0.43/0.60      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 0.43/0.60  thf('173', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.43/0.60         = (k2_struct_0 @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)], ['33', '34', '35', '36', '37', '38'])).
% 0.43/0.60  thf('174', plain,
% 0.43/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60         (k1_zfmisc_1 @ 
% 0.43/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.43/0.60        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.43/0.60      inference('demod', [status(thm)], ['172', '173'])).
% 0.43/0.60  thf('175', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.43/0.60        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60           (k1_zfmisc_1 @ 
% 0.43/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.60      inference('sup-', [status(thm)], ['165', '174'])).
% 0.43/0.60  thf('176', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('177', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.43/0.60        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60           (k1_zfmisc_1 @ 
% 0.43/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.60      inference('demod', [status(thm)], ['175', '176'])).
% 0.43/0.60  thf('178', plain,
% 0.43/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.43/0.60      inference('simplify', [status(thm)], ['177'])).
% 0.43/0.60  thf('179', plain,
% 0.43/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.60         (((k2_relset_1 @ X10 @ X9 @ X11) != (X9))
% 0.43/0.60          | ~ (v2_funct_1 @ X11)
% 0.43/0.60          | ((k2_tops_2 @ X10 @ X9 @ X11) = (k2_funct_1 @ X11))
% 0.43/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 0.43/0.60          | ~ (v1_funct_2 @ X11 @ X10 @ X9)
% 0.43/0.60          | ~ (v1_funct_1 @ X11))),
% 0.43/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.43/0.60  thf('180', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.43/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.60             (u1_struct_0 @ sk_A))
% 0.43/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['178', '179'])).
% 0.43/0.60  thf('181', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['103'])).
% 0.43/0.60  thf('182', plain,
% 0.43/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.60        (u1_struct_0 @ sk_A))),
% 0.43/0.60      inference('simplify', [status(thm)], ['88'])).
% 0.43/0.60  thf('183', plain,
% 0.43/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.43/0.60      inference('demod', [status(thm)], ['180', '181', '182'])).
% 0.43/0.60  thf('184', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['162'])).
% 0.43/0.60  thf('185', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.43/0.60      inference('clc', [status(thm)], ['149', '150'])).
% 0.43/0.60  thf('186', plain,
% 0.43/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.43/0.60        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.43/0.60      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.43/0.60  thf('187', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.43/0.60      inference('sup-', [status(thm)], ['164', '186'])).
% 0.43/0.60  thf('188', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.60  thf('189', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.43/0.60      inference('demod', [status(thm)], ['187', '188'])).
% 0.43/0.60  thf('190', plain,
% 0.43/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['189'])).
% 0.43/0.60  thf(t65_funct_1, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.60       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.43/0.60  thf('191', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (v2_funct_1 @ X0)
% 0.43/0.60          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.43/0.60          | ~ (v1_funct_1 @ X0)
% 0.43/0.60          | ~ (v1_relat_1 @ X0))),
% 0.43/0.60      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.43/0.60  thf('192', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('193', plain,
% 0.43/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.43/0.60      inference('simplify', [status(thm)], ['54'])).
% 0.43/0.60  thf('194', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (~ (v2_funct_1 @ X4)
% 0.43/0.60          | ((k2_relset_1 @ X6 @ X5 @ X4) != (X5))
% 0.43/0.60          | (m1_subset_1 @ (k2_funct_1 @ X4) @ 
% 0.43/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.43/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.43/0.60          | ~ (v1_funct_2 @ X4 @ X6 @ X5)
% 0.43/0.60          | ~ (v1_funct_1 @ X4))),
% 0.43/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.43/0.60  thf('195', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.43/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.43/0.60             (u1_struct_0 @ sk_A))
% 0.43/0.60        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60           (k1_zfmisc_1 @ 
% 0.43/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.43/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['193', '194'])).
% 0.43/0.60  thf('196', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['103'])).
% 0.43/0.60  thf('197', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('198', plain,
% 0.43/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.60        (u1_struct_0 @ sk_A))),
% 0.43/0.60      inference('simplify', [status(thm)], ['88'])).
% 0.43/0.60  thf('199', plain,
% 0.43/0.60      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.43/0.60         (u1_struct_0 @ sk_A))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.43/0.60      inference('sup+', [status(thm)], ['197', '198'])).
% 0.43/0.60  thf('200', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('201', plain,
% 0.43/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.43/0.60        (u1_struct_0 @ sk_A))),
% 0.43/0.60      inference('demod', [status(thm)], ['199', '200'])).
% 0.43/0.60  thf('202', plain,
% 0.43/0.60      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60         (k1_zfmisc_1 @ 
% 0.43/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.43/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('demod', [status(thm)], ['195', '196', '201'])).
% 0.43/0.60  thf('203', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('204', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.43/0.60      inference('clc', [status(thm)], ['149', '150'])).
% 0.43/0.60  thf('205', plain,
% 0.43/0.60      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.43/0.60      inference('sup+', [status(thm)], ['203', '204'])).
% 0.43/0.60  thf('206', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('207', plain,
% 0.43/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.43/0.60      inference('demod', [status(thm)], ['205', '206'])).
% 0.43/0.60  thf('208', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['162'])).
% 0.43/0.60  thf('209', plain,
% 0.43/0.60      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60         (k1_zfmisc_1 @ 
% 0.43/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.43/0.60        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.43/0.60      inference('demod', [status(thm)], ['202', '207', '208'])).
% 0.43/0.60  thf('210', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.60        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60           (k1_zfmisc_1 @ 
% 0.43/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 0.43/0.60      inference('sup-', [status(thm)], ['192', '209'])).
% 0.43/0.60  thf('211', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.60  thf('212', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60           (k1_zfmisc_1 @ 
% 0.43/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 0.43/0.60      inference('demod', [status(thm)], ['210', '211'])).
% 0.43/0.60  thf('213', plain,
% 0.43/0.60      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.43/0.60      inference('simplify', [status(thm)], ['212'])).
% 0.43/0.60  thf('214', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('215', plain,
% 0.43/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.60         (~ (l1_pre_topc @ X12)
% 0.43/0.60          | ~ (v3_tops_2 @ X13 @ X14 @ X12)
% 0.43/0.60          | (v5_pre_topc @ X13 @ X14 @ X12)
% 0.43/0.60          | ~ (m1_subset_1 @ X13 @ 
% 0.43/0.60               (k1_zfmisc_1 @ 
% 0.43/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))))
% 0.43/0.60          | ~ (v1_funct_2 @ X13 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X12))
% 0.43/0.60          | ~ (v1_funct_1 @ X13)
% 0.43/0.60          | ~ (l1_pre_topc @ X14))),
% 0.43/0.60      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.43/0.60  thf('216', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         (~ (m1_subset_1 @ X2 @ 
% 0.43/0.60             (k1_zfmisc_1 @ 
% 0.43/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.43/0.60          | ~ (l1_struct_0 @ X0)
% 0.43/0.60          | ~ (l1_pre_topc @ X1)
% 0.43/0.60          | ~ (v1_funct_1 @ X2)
% 0.43/0.60          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.43/0.60          | (v5_pre_topc @ X2 @ X1 @ X0)
% 0.43/0.60          | ~ (v3_tops_2 @ X2 @ X1 @ X0)
% 0.43/0.60          | ~ (l1_pre_topc @ X0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['214', '215'])).
% 0.43/0.60  thf('217', plain,
% 0.43/0.60      ((~ (l1_pre_topc @ sk_B)
% 0.43/0.60        | ~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 0.43/0.60        | (v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 0.43/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.43/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['213', '216'])).
% 0.43/0.60  thf('218', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('219', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('220', plain,
% 0.43/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.43/0.60      inference('simplify', [status(thm)], ['177'])).
% 0.43/0.60  thf('221', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (~ (v2_funct_1 @ X4)
% 0.43/0.60          | ((k2_relset_1 @ X6 @ X5 @ X4) != (X5))
% 0.43/0.60          | (v1_funct_2 @ (k2_funct_1 @ X4) @ X5 @ X6)
% 0.43/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.43/0.60          | ~ (v1_funct_2 @ X4 @ X6 @ X5)
% 0.43/0.60          | ~ (v1_funct_1 @ X4))),
% 0.43/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.43/0.60  thf('222', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.43/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.60             (u1_struct_0 @ sk_A))
% 0.43/0.60        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['220', '221'])).
% 0.43/0.60  thf('223', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['103'])).
% 0.43/0.60  thf('224', plain,
% 0.43/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.60        (u1_struct_0 @ sk_A))),
% 0.43/0.60      inference('simplify', [status(thm)], ['88'])).
% 0.43/0.60  thf('225', plain,
% 0.43/0.60      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('demod', [status(thm)], ['222', '223', '224'])).
% 0.43/0.60  thf('226', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.43/0.60      inference('clc', [status(thm)], ['149', '150'])).
% 0.43/0.60  thf('227', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['162'])).
% 0.43/0.60  thf('228', plain,
% 0.43/0.60      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.43/0.60      inference('demod', [status(thm)], ['225', '226', '227'])).
% 0.43/0.60  thf('229', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.60        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['219', '228'])).
% 0.43/0.60  thf('230', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.60  thf('231', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.43/0.60      inference('demod', [status(thm)], ['229', '230'])).
% 0.43/0.60  thf('232', plain,
% 0.43/0.60      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.43/0.60        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.60      inference('simplify', [status(thm)], ['231'])).
% 0.43/0.60  thf('233', plain,
% 0.43/0.60      (![X7 : $i]:
% 0.43/0.60         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.60  thf('234', plain,
% 0.43/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.43/0.60      inference('simplify', [status(thm)], ['177'])).
% 0.43/0.60  thf('235', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (~ (v2_funct_1 @ X4)
% 0.43/0.60          | ((k2_relset_1 @ X6 @ X5 @ X4) != (X5))
% 0.43/0.60          | (v1_funct_1 @ (k2_funct_1 @ X4))
% 0.43/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X5)))
% 0.43/0.60          | ~ (v1_funct_2 @ X4 @ X6 @ X5)
% 0.43/0.60          | ~ (v1_funct_1 @ X4))),
% 0.43/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.43/0.60  thf('236', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.43/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.60             (u1_struct_0 @ sk_A))
% 0.43/0.60        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['234', '235'])).
% 0.43/0.60  thf('237', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['103'])).
% 0.43/0.60  thf('238', plain,
% 0.43/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.60        (u1_struct_0 @ sk_A))),
% 0.43/0.60      inference('simplify', [status(thm)], ['88'])).
% 0.43/0.60  thf('239', plain,
% 0.43/0.60      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.43/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 0.43/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('demod', [status(thm)], ['236', '237', '238'])).
% 0.43/0.60  thf('240', plain,
% 0.43/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.43/0.60         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.43/0.60      inference('clc', [status(thm)], ['149', '150'])).
% 0.43/0.60  thf('241', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.43/0.60      inference('simplify', [status(thm)], ['162'])).
% 0.43/0.60  thf('242', plain,
% 0.43/0.60      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.43/0.60        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.43/0.60      inference('demod', [status(thm)], ['239', '240', '241'])).
% 0.43/0.60  thf('243', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.60        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.43/0.60      inference('sup-', [status(thm)], ['233', '242'])).
% 0.43/0.60  thf('244', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['111', '112'])).
% 0.43/0.60  thf('245', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.43/0.60      inference('demod', [status(thm)], ['243', '244'])).
% 0.43/0.60  thf('246', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['245'])).
% 0.43/0.60  thf('247', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('248', plain, ((l1_struct_0 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('249', plain,
% 0.43/0.60      ((~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 0.43/0.60        | (v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B))),
% 0.43/0.60      inference('demod', [status(thm)],
% 0.43/0.60                ['217', '218', '232', '246', '247', '248'])).
% 0.43/0.60  thf('250', plain,
% 0.43/0.60      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.43/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.43/0.60        | (v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['191', '249'])).
% 0.43/0.60  thf('251', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('252', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ 
% 0.43/0.60        (k1_zfmisc_1 @ 
% 0.43/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(cc1_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.60       ( v1_relat_1 @ C ) ))).
% 0.43/0.60  thf('253', plain,
% 0.43/0.60      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.60         ((v1_relat_1 @ X1)
% 0.43/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.43/0.60  thf('254', plain, ((v1_relat_1 @ sk_C)),
% 0.43/0.60      inference('sup-', [status(thm)], ['252', '253'])).
% 0.43/0.60  thf('255', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('256', plain, ((v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('demod', [status(thm)], ['22', '23', '24', '25', '26', '27'])).
% 0.43/0.60  thf('257', plain,
% 0.43/0.60      ((v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)),
% 0.43/0.60      inference('demod', [status(thm)], ['250', '251', '254', '255', '256'])).
% 0.43/0.60  thf('258', plain,
% 0.43/0.60      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.43/0.60        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.43/0.60        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.43/0.60      inference('demod', [status(thm)],
% 0.43/0.60                ['107', '137', '151', '163', '190', '257'])).
% 0.43/0.60  thf('259', plain, ((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.43/0.60      inference('simplify', [status(thm)], ['258'])).
% 0.43/0.60  thf('260', plain, ($false), inference('demod', [status(thm)], ['45', '259'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
