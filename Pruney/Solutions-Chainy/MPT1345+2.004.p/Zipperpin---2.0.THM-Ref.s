%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QLGmjb47rz

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:29 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  207 (1596 expanded)
%              Number of leaves         :   31 ( 497 expanded)
%              Depth                    :   19
%              Number of atoms          : 2162 (35091 expanded)
%              Number of equality atoms :  102 ( 468 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
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
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X6 @ X8 )
       != X6 )
      | ~ ( v2_funct_1 @ X8 )
      | ( ( k2_tops_2 @ X7 @ X6 @ X8 )
        = ( k2_funct_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
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
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
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

thf('20',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v3_tops_2 @ X10 @ X11 @ X9 )
      | ( v2_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
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
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('30',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v3_tops_2 @ X10 @ X11 @ X9 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 )
        = ( k2_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39'])).

thf('41',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','43'])).

thf('45',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','45'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X6 @ X8 )
       != X6 )
      | ~ ( v2_funct_1 @ X8 )
      | ( ( k2_tops_2 @ X7 @ X6 @ X8 )
        = ( k2_funct_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('60',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39'])).

thf('62',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('65',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','66'])).

thf('68',plain,(
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

thf('69',plain,
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('72',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('76',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('78',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X12 @ X13 @ X14 ) @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('85',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v3_tops_2 @ X10 @ X11 @ X9 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) @ X10 ) @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('93',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','78','85','95','96'])).

thf('98',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','66'])).

thf('100',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X6 @ X8 )
       != X6 )
      | ~ ( v2_funct_1 @ X8 )
      | ( ( k2_tops_2 @ X7 @ X6 @ X8 )
        = ( k2_funct_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('103',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('108',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('112',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','112'])).

thf('114',plain,(
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

thf('115',plain,(
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

thf('116',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39'])).

thf('125',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('126',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','119','120','121','122','123','124','125'])).

thf('127',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
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

thf('129',plain,(
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

thf('130',plain,
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
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['117','118'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('136',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39'])).

thf('137',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('138',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','127','141'])).

thf('143',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['98','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['117','118'])).

thf('145',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v3_tops_2 @ X10 @ X11 @ X9 )
      | ( v5_pre_topc @ X10 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('149',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['149','150','151','152','153','154'])).

thf('156',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('157',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
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

thf('160',plain,
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
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['117','118'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['23','24','25','26','27','28'])).

thf('166',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39'])).

thf('167',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('168',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['160','161','162','163','164','165','166','167'])).

thf('169',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','146','155','156','157','171'])).

thf('173',plain,(
    v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    $false ),
    inference(demod,[status(thm)],['46','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QLGmjb47rz
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 239 iterations in 0.169s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(d3_struct_0, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf(t70_tops_2, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                 ( m1_subset_1 @
% 0.46/0.63                   C @ 
% 0.46/0.63                   ( k1_zfmisc_1 @
% 0.46/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63               ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.46/0.63                 ( v3_tops_2 @
% 0.46/0.63                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.46/0.63                   B @ A ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( l1_pre_topc @ A ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.63              ( ![C:$i]:
% 0.46/0.63                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                    ( v1_funct_2 @
% 0.46/0.63                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                    ( m1_subset_1 @
% 0.46/0.63                      C @ 
% 0.46/0.63                      ( k1_zfmisc_1 @
% 0.46/0.63                        ( k2_zfmisc_1 @
% 0.46/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 0.46/0.63                    ( v3_tops_2 @
% 0.46/0.63                      ( k2_tops_2 @
% 0.46/0.63                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.46/0.63                      B @ A ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (~ (v3_tops_2 @ 
% 0.46/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.63          sk_B @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      ((~ (v3_tops_2 @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.63           sk_B @ sk_A)
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf('3', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_l1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.63  thf('4', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.63  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (~ (v3_tops_2 @ 
% 0.46/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.63          sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['2', '5'])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_C @ 
% 0.46/0.63         (k1_zfmisc_1 @ 
% 0.46/0.63          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.63  thf(d4_tops_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.63         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X7 @ X6 @ X8) != (X6))
% 0.46/0.63          | ~ (v2_funct_1 @ X8)
% 0.46/0.63          | ((k2_tops_2 @ X7 @ X6 @ X8) = (k2_funct_1 @ X8))
% 0.46/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.46/0.63          | ~ (v1_funct_2 @ X8 @ X7 @ X6)
% 0.46/0.63          | ~ (v1_funct_1 @ X8))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['13', '14', '19'])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d5_tops_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( l1_pre_topc @ B ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                 ( m1_subset_1 @
% 0.46/0.63                   C @ 
% 0.46/0.63                   ( k1_zfmisc_1 @
% 0.46/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 0.46/0.63                 ( ( ( k1_relset_1 @
% 0.46/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.63                     ( k2_struct_0 @ A ) ) & 
% 0.46/0.63                   ( ( k2_relset_1 @
% 0.46/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.63                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.63                   ( v5_pre_topc @
% 0.46/0.63                     ( k2_tops_2 @
% 0.46/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.46/0.63                     B @ A ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X9)
% 0.46/0.63          | ~ (v3_tops_2 @ X10 @ X11 @ X9)
% 0.46/0.63          | (v2_funct_1 @ X10)
% 0.46/0.63          | ~ (m1_subset_1 @ X10 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.46/0.63          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.46/0.63          | ~ (v1_funct_1 @ X10)
% 0.46/0.63          | ~ (l1_pre_topc @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v2_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.63  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('27', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '29'])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X9)
% 0.46/0.63          | ~ (v3_tops_2 @ X10 @ X11 @ X9)
% 0.46/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10)
% 0.46/0.63              = (k2_struct_0 @ X9))
% 0.46/0.63          | ~ (m1_subset_1 @ X10 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.46/0.63          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.46/0.63          | ~ (v1_funct_1 @ X10)
% 0.46/0.63          | ~ (l1_pre_topc @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            = (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('38', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35', '36', '37', '38', '39'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['31', '40'])).
% 0.46/0.63  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['30', '43'])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.46/0.63  thf('46', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['6', '45'])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k2_tops_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.46/0.63         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.46/0.63         ( m1_subset_1 @
% 0.46/0.63           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.46/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k2_tops_2 @ X12 @ X13 @ X14) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12)))
% 0.46/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.46/0.63          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.46/0.63          | ~ (v1_funct_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (m1_subset_1 @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.63           (k1_zfmisc_1 @ 
% 0.46/0.63            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.63  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X7 @ X6 @ X8) != (X6))
% 0.46/0.63          | ~ (v2_funct_1 @ X8)
% 0.46/0.63          | ((k2_tops_2 @ X7 @ X6 @ X8) = (k2_funct_1 @ X8))
% 0.46/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.46/0.63          | ~ (v1_funct_2 @ X8 @ X7 @ X6)
% 0.46/0.63          | ~ (v1_funct_1 @ X8))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.63  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.46/0.63  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35', '36', '37', '38', '39'])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.63  thf('63', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            = (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['52', '62'])).
% 0.46/0.63  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            = (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('67', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['49', '50', '51', '66'])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X9)
% 0.46/0.63          | ((k1_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10)
% 0.46/0.63              != (k2_struct_0 @ X11))
% 0.46/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10)
% 0.46/0.63              != (k2_struct_0 @ X9))
% 0.46/0.63          | ~ (v2_funct_1 @ X10)
% 0.46/0.63          | ~ (v5_pre_topc @ X10 @ X11 @ X9)
% 0.46/0.63          | ~ (v5_pre_topc @ 
% 0.46/0.63               (k2_tops_2 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10) @ 
% 0.46/0.63               X9 @ X11)
% 0.46/0.63          | (v3_tops_2 @ X10 @ X11 @ X9)
% 0.46/0.63          | ~ (m1_subset_1 @ X10 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.46/0.63          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.46/0.63          | ~ (v1_funct_1 @ X10)
% 0.46/0.63          | ~ (l1_pre_topc @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.63        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63             (u1_struct_0 @ sk_A))
% 0.46/0.63        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.63        | ~ (v5_pre_topc @ 
% 0.46/0.63             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63              (k2_funct_1 @ sk_C)) @ 
% 0.46/0.63             sk_A @ sk_B)
% 0.46/0.63        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('71', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         ((v1_funct_1 @ (k2_tops_2 @ X12 @ X13 @ X14))
% 0.46/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.46/0.63          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.46/0.63          | ~ (v1_funct_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | (v1_funct_1 @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.63  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('75', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      ((v1_funct_1 @ 
% 0.46/0.63        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.46/0.63  thf('77', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.46/0.63  thf('78', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         ((v1_funct_2 @ (k2_tops_2 @ X12 @ X13 @ X14) @ X13 @ X12)
% 0.46/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.46/0.63          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.46/0.63          | ~ (v1_funct_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.46/0.63  thf('81', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v1_funct_2 @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.63           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.63  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('84', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('85', plain,
% 0.46/0.63      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.46/0.63  thf('86', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('87', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X9)
% 0.46/0.63          | ~ (v3_tops_2 @ X10 @ X11 @ X9)
% 0.46/0.63          | (v5_pre_topc @ 
% 0.46/0.63             (k2_tops_2 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9) @ X10) @ 
% 0.46/0.63             X9 @ X11)
% 0.46/0.63          | ~ (m1_subset_1 @ X10 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.46/0.63          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.46/0.63          | ~ (v1_funct_1 @ X10)
% 0.46/0.63          | ~ (l1_pre_topc @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.63  thf('88', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v5_pre_topc @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.46/0.63           sk_B @ sk_A)
% 0.46/0.63        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['86', '87'])).
% 0.46/0.63  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('91', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('92', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('93', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('95', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['88', '89', '90', '91', '92', '93', '94'])).
% 0.46/0.63  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('97', plain,
% 0.46/0.63      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.63        | ~ (v5_pre_topc @ 
% 0.46/0.63             (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63              (k2_funct_1 @ sk_C)) @ 
% 0.46/0.63             sk_A @ sk_B)
% 0.46/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['69', '70', '78', '85', '95', '96'])).
% 0.46/0.63  thf('98', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('99', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['49', '50', '51', '66'])).
% 0.46/0.63  thf('100', plain,
% 0.46/0.63      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X7 @ X6 @ X8) != (X6))
% 0.46/0.63          | ~ (v2_funct_1 @ X8)
% 0.46/0.63          | ((k2_tops_2 @ X7 @ X6 @ X8) = (k2_funct_1 @ X8))
% 0.46/0.63          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.46/0.63          | ~ (v1_funct_2 @ X8 @ X7 @ X6)
% 0.46/0.63          | ~ (v1_funct_1 @ X8))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.63  thf('101', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63             (u1_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.63  thf('102', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['76', '77'])).
% 0.46/0.63  thf('103', plain,
% 0.46/0.63      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63        (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.46/0.63  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t65_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.63  thf('105', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.63  thf('106', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['104', '105'])).
% 0.46/0.63  thf('107', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc1_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( v1_relat_1 @ C ) ))).
% 0.46/0.63  thf('108', plain,
% 0.46/0.63      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.63         ((v1_relat_1 @ X1)
% 0.46/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.63  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('sup-', [status(thm)], ['107', '108'])).
% 0.46/0.63  thf('110', plain,
% 0.46/0.63      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)) | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['106', '109'])).
% 0.46/0.63  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.46/0.63  thf('112', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['110', '111'])).
% 0.46/0.63  thf('113', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['101', '102', '103', '112'])).
% 0.46/0.63  thf('114', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t63_tops_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_struct_0 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( l1_struct_0 @ B ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                 ( m1_subset_1 @
% 0.46/0.63                   C @ 
% 0.46/0.63                   ( k1_zfmisc_1 @
% 0.46/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63               ( ( ( ( k2_relset_1 @
% 0.46/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.63                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.63                 ( v2_funct_1 @
% 0.46/0.63                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('115', plain,
% 0.46/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.63         (~ (l1_struct_0 @ X18)
% 0.46/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20)
% 0.46/0.63              != (k2_struct_0 @ X18))
% 0.46/0.63          | ~ (v2_funct_1 @ X20)
% 0.46/0.63          | (v2_funct_1 @ 
% 0.46/0.63             (k2_tops_2 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20))
% 0.46/0.63          | ~ (m1_subset_1 @ X20 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.46/0.63          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.46/0.63          | ~ (v1_funct_1 @ X20)
% 0.46/0.63          | ~ (l1_struct_0 @ X19))),
% 0.46/0.63      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.46/0.63  thf('116', plain,
% 0.46/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v2_funct_1 @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.63  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('118', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.63  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.63  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('121', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('122', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.46/0.63  thf('124', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35', '36', '37', '38', '39'])).
% 0.46/0.63  thf('125', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('126', plain,
% 0.46/0.63      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['116', '119', '120', '121', '122', '123', '124', '125'])).
% 0.46/0.63  thf('127', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.63  thf('128', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t62_tops_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_struct_0 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                 ( m1_subset_1 @
% 0.46/0.63                   C @ 
% 0.46/0.63                   ( k1_zfmisc_1 @
% 0.46/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63               ( ( ( ( k2_relset_1 @
% 0.46/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.63                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.63                 ( ( ( k1_relset_1 @
% 0.46/0.63                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.63                       ( k2_tops_2 @
% 0.46/0.63                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.63                   ( ( k2_relset_1 @
% 0.46/0.63                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.63                       ( k2_tops_2 @
% 0.46/0.63                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.46/0.63                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('129', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.63         ((v2_struct_0 @ X15)
% 0.46/0.63          | ~ (l1_struct_0 @ X15)
% 0.46/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17)
% 0.46/0.63              != (k2_struct_0 @ X15))
% 0.46/0.63          | ~ (v2_funct_1 @ X17)
% 0.46/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16) @ 
% 0.46/0.63              (k2_tops_2 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17))
% 0.46/0.63              = (k2_struct_0 @ X16))
% 0.46/0.63          | ~ (m1_subset_1 @ X17 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))))
% 0.46/0.63          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.46/0.63          | ~ (v1_funct_1 @ X17)
% 0.46/0.63          | ~ (l1_struct_0 @ X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.46/0.63  thf('130', plain,
% 0.46/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.63            = (k2_struct_0 @ sk_A))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['128', '129'])).
% 0.46/0.63  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.63  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('133', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('134', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.46/0.63  thf('136', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35', '36', '37', '38', '39'])).
% 0.46/0.63  thf('137', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('138', plain,
% 0.46/0.63      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['130', '131', '132', '133', '134', '135', '136', '137'])).
% 0.46/0.63  thf('139', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['138'])).
% 0.46/0.63  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('141', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['139', '140'])).
% 0.46/0.63  thf('142', plain,
% 0.46/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.46/0.63        | ((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['113', '127', '141'])).
% 0.46/0.63  thf('143', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['98', '142'])).
% 0.46/0.63  thf('144', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.63  thf('145', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.46/0.63      inference('demod', [status(thm)], ['143', '144'])).
% 0.46/0.63  thf('146', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['145'])).
% 0.46/0.63  thf('147', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('148', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X9)
% 0.46/0.63          | ~ (v3_tops_2 @ X10 @ X11 @ X9)
% 0.46/0.63          | (v5_pre_topc @ X10 @ X11 @ X9)
% 0.46/0.63          | ~ (m1_subset_1 @ X10 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))))
% 0.46/0.63          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X9))
% 0.46/0.63          | ~ (v1_funct_1 @ X10)
% 0.46/0.63          | ~ (l1_pre_topc @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_tops_2])).
% 0.46/0.63  thf('149', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.46/0.63        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['147', '148'])).
% 0.46/0.63  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('152', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('153', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('154', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('155', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['149', '150', '151', '152', '153', '154'])).
% 0.46/0.63  thf('156', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.63  thf('157', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['139', '140'])).
% 0.46/0.63  thf('158', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('159', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.63         ((v2_struct_0 @ X15)
% 0.46/0.63          | ~ (l1_struct_0 @ X15)
% 0.46/0.63          | ((k2_relset_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17)
% 0.46/0.63              != (k2_struct_0 @ X15))
% 0.46/0.63          | ~ (v2_funct_1 @ X17)
% 0.46/0.63          | ((k1_relset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16) @ 
% 0.46/0.63              (k2_tops_2 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15) @ X17))
% 0.46/0.63              = (k2_struct_0 @ X15))
% 0.46/0.63          | ~ (m1_subset_1 @ X17 @ 
% 0.46/0.63               (k1_zfmisc_1 @ 
% 0.46/0.63                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))))
% 0.46/0.63          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X15))
% 0.46/0.63          | ~ (v1_funct_1 @ X17)
% 0.46/0.63          | ~ (l1_struct_0 @ X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.46/0.63  thf('160', plain,
% 0.46/0.63      ((~ (l1_struct_0 @ sk_A)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.63            = (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['158', '159'])).
% 0.46/0.63  thf('161', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['117', '118'])).
% 0.46/0.63  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('163', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('164', plain,
% 0.46/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['23', '24', '25', '26', '27', '28'])).
% 0.46/0.63  thf('166', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '35', '36', '37', '38', '39'])).
% 0.46/0.63  thf('167', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf('168', plain,
% 0.46/0.63      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63          (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.63        | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['160', '161', '162', '163', '164', '165', '166', '167'])).
% 0.46/0.63  thf('169', plain,
% 0.46/0.63      (((v2_struct_0 @ sk_B)
% 0.46/0.63        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['168'])).
% 0.46/0.63  thf('170', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('171', plain,
% 0.46/0.63      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('clc', [status(thm)], ['169', '170'])).
% 0.46/0.63  thf('172', plain,
% 0.46/0.63      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.46/0.63        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['97', '146', '155', '156', '157', '171'])).
% 0.46/0.63  thf('173', plain, ((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.46/0.63      inference('simplify', [status(thm)], ['172'])).
% 0.46/0.63  thf('174', plain, ($false), inference('demod', [status(thm)], ['46', '173'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
