%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1347+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XeMUBkHsYF

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:32 EST 2020

% Result     : Theorem 44.40s
% Output     : Refutation 44.40s
% Verified   : 
% Statistics : Number of formulae       :  661 (6847 expanded)
%              Number of leaves         :   51 (1972 expanded)
%              Depth                    :   26
%              Number of atoms          : 8995 (205608 expanded)
%              Number of equality atoms :  422 (7417 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t72_tops_2,conjecture,(
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
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( v4_pre_topc @ D @ A )
                      <=> ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) ) )).

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
                <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ A ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( v4_pre_topc @ D @ A )
                        <=> ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_tops_2])).

thf('0',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X54: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X54 @ sk_A )
      | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ( v4_pre_topc @ X54 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('18',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('20',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v3_tops_2 @ X15 @ X16 @ X14 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X15 )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
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
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('31',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v3_tops_2 @ X15 @ X16 @ X14 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
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
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','30','40'])).

thf('42',plain,
    ( ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_B ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('44',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v3_tops_2 @ X15 @ X16 @ X14 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X15 )
        = ( k2_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('55',plain,
    ( ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','56'])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('60',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ X43 @ ( k1_relat_1 @ X44 ) )
      | ( r1_tarski @ X43 @ ( k10_relat_1 @ X44 @ ( k9_relat_1 @ X44 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('69',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v2_funct_1 @ X47 )
      | ( r1_tarski @ ( k10_relat_1 @ X47 @ ( k9_relat_1 @ X47 @ X48 ) ) @ X48 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('70',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('75',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('78',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k8_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k10_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','86'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('88',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,
    ( ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','91'])).

thf('93',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('94',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('96',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    ! [X54: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
      | ~ ( v4_pre_topc @ X54 @ sk_A )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ~ ( v4_pre_topc @ X54 @ sk_A ) )
   <= ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('101',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('102',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('104',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X45 @ ( k2_relat_1 @ X46 ) )
      | ( ( k9_relat_1 @ X46 @ ( k10_relat_1 @ X46 @ X45 ) )
        = X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('107',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('110',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,
    ( ( m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['105','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('116',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('118',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('124',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      | ( ( u1_struct_0 @ sk_B )
        = ( k2_relat_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','125'])).

thf('127',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('128',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('131',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['130','135'])).

thf('137',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['129','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('139',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('141',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100','128','143'])).

thf('145',plain,
    ( ( ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B )
      | ~ ( v4_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','144'])).

thf('146',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('147',plain,
    ( ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('149',plain,
    ( ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
      | ( v4_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('152',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('153',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('154',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
      | ( v4_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,
    ( ( ( v4_pre_topc @ sk_D_1 @ sk_A )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('157',plain,
    ( ( ( v4_pre_topc @ sk_D_1 @ sk_A )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['145','157'])).

thf('159',plain,
    ( ~ ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('161',plain,
    ( ~ ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('163',plain,
    ( ~ ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('165',plain,
    ( ~ ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v4_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['158','165'])).

thf('167',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('169',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('170',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('171',plain,
    ( ( ( v4_pre_topc @ sk_D_1 @ sk_A )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('172',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('173',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('174',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v3_tops_2 @ X15 @ X16 @ X14 )
      | ( v5_pre_topc @ X15 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('178',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('185',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('186',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( v4_pre_topc @ X9 @ X6 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['187','188','189','190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['184','194'])).

thf('196',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('197',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) @ sk_A )
        | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['174','197'])).

thf('199',plain,
    ( ( ( v4_pre_topc @ sk_D_1 @ sk_A )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_D_1 ) ) @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['171','198'])).

thf('200',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('201',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('202',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('203',plain,
    ( ( r1_tarski @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( r1_tarski @ sk_D_1 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['200','203'])).

thf('205',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('206',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('207',plain,
    ( ( r1_tarski @ sk_D_1 @ ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ X43 @ ( k1_relat_1 @ X44 ) )
      | ( r1_tarski @ X43 @ ( k10_relat_1 @ X44 @ ( k9_relat_1 @ X44 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('209',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ sk_D_1 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_D_1 ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('211',plain,
    ( ( r1_tarski @ sk_D_1 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_D_1 ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('213',plain,
    ( ( ( sk_D_1
        = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_D_1 ) ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('217',plain,
    ( ( sk_D_1
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_D_1 ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['213','214','215','216'])).

thf('218',plain,
    ( ( ( v4_pre_topc @ sk_D_1 @ sk_A )
      | ( v4_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['199','217'])).

thf('219',plain,
    ( ( v4_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170','219'])).

thf('221',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('223',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('224',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('226',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('228',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['228','229','230','231','232'])).

thf('234',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('235',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['225','235'])).

thf('237',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('238',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['224','238'])).

thf('240',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X45 @ ( k2_relat_1 @ X46 ) )
      | ( ( k9_relat_1 @ X46 @ ( k10_relat_1 @ X46 @ X45 ) )
        = X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('241',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('247',plain,
    ( ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ( v4_pre_topc @ X54 @ sk_A ) )
   <= ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ( v4_pre_topc @ X54 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('248',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ( v4_pre_topc @ X54 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,
    ( ! [X0: $i] :
        ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
        | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) ) @ sk_B ) )
   <= ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ( v4_pre_topc @ X54 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['245','248'])).

thf('250',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['244','249'])).

thf('251',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ( v4_pre_topc @ ( sk_D @ X7 @ X6 @ X8 ) @ X6 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('253',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['253','254','255','256','257'])).

thf('259',plain,
    ( ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['250','258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('261',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ ( sk_D @ X7 @ X6 @ X8 ) ) @ X8 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('262',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['262','263','264','265','266','267'])).

thf('269',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['259','268'])).

thf('270',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('271',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('272',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('273',plain,(
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

thf('274',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X11 @ X13 )
       != X11 )
      | ~ ( v2_funct_1 @ X13 )
      | ( ( k2_tops_2 @ X12 @ X11 @ X13 )
        = ( k2_funct_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('275',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['275','276','277'])).

thf('279',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( u1_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['272','278'])).

thf('280',plain,
    ( ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k2_struct_0 @ sk_B )
       != ( u1_struct_0 @ sk_B ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['271','279'])).

thf('281',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['270','280'])).

thf('282',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('283',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,(
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

thf('286',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('287',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('291',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['284','290'])).

thf('292',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('293',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('294',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      | ( ( u1_struct_0 @ sk_B )
        = ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('296',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['291','296'])).

thf('298',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('299',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('300',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('301',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['298','301'])).

thf('303',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('305',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['302','303','304'])).

thf('306',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('307',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v1_funct_2 @ X1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['297','307'])).

thf('309',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('310',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X17 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('312',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['309','315'])).

thf('317',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('318',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('319',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('320',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X17 @ X18 @ X19 ) @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('322',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('326',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['319','325'])).

thf('327',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['318','326'])).

thf('328',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('329',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['327','328'])).

thf('330',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['317','329'])).

thf('331',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ( ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['308','316','330','331'])).

thf('333',plain,
    ( ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ~ ( v4_pre_topc @ X54 @ sk_A ) )
   <= ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ),
    inference(split,[status(esa)],['97'])).

thf('334',plain,
    ( ( ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['332','333'])).

thf('335',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('336',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('337',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('338',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['337','338'])).

thf('340',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('341',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['339','340'])).

thf('342',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['336','341'])).

thf('343',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('344',plain,
    ( ! [X0: $i] :
        ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,
    ( ( ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['334','335','344'])).

thf('346',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['291','296'])).

thf('347',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('348',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('349',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ( v4_pre_topc @ ( sk_D @ X7 @ X6 @ X8 ) @ X6 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('350',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ( v4_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('351',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ( v4_pre_topc @ ( sk_D @ X1 @ X0 @ sk_B ) @ X0 )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['347','350'])).

thf('352',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('354',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ( v4_pre_topc @ ( sk_D @ X1 @ X0 @ sk_B ) @ X0 )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['351','352','353'])).

thf('355',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('356',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ( v4_pre_topc @ ( sk_D @ X1 @ X0 @ sk_B ) @ X0 )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v1_funct_2 @ X1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['354','355'])).

thf('357',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['346','356'])).

thf('358',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['309','315'])).

thf('359',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['317','329'])).

thf('360',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['357','358','359','360'])).

thf('362',plain,
    ( ( ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
      | ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['345','361'])).

thf('363',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['291','296'])).

thf('364',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k8_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k10_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('365',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['363','364'])).

thf('366',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('367',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('368',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k9_relat_1 @ X49 @ X50 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X49 ) @ X50 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('369',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('371',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['369','370'])).

thf('372',plain,
    ( ! [X0: $i] :
        ( ( k9_relat_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
   <= ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['366','371'])).

thf('373',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['365','372'])).

thf('374',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('375',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('376',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ ( sk_D @ X7 @ X6 @ X8 ) ) @ X8 )
      | ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('377',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['375','376'])).

thf('378',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( sk_D @ X1 @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( l1_pre_topc @ X0 )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['374','377'])).

thf('379',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('381',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( sk_D @ X1 @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( l1_pre_topc @ X0 )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['378','379','380'])).

thf('382',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('383',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('384',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( sk_D @ X1 @ X0 @ sk_B ) ) @ sk_B )
        | ~ ( l1_pre_topc @ X0 )
        | ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['381','382','383'])).

thf('385',plain,
    ( ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['373','384'])).

thf('386',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['309','315'])).

thf('387',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['317','329'])).

thf('388',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['291','296'])).

thf('389',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('390',plain,
    ( ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ) @ sk_B )
      | ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['385','386','387','388','389'])).

thf('391',plain,
    ( ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['362','390'])).

thf('392',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('393',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('394',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('395',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['393','394'])).

thf('396',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('397',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('398',plain,
    ( ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['396','397'])).

thf('399',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('400',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['398','399'])).

thf('401',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['395','400'])).

thf('402',plain,
    ( ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['392','401'])).

thf('403',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('404',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['402','403'])).

thf('405',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('406',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['404','405'])).

thf('407',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('408',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['393','394'])).

thf('409',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('410',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('411',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('412',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['410','411'])).

thf('413',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['409','412'])).

thf('414',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('415',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['413','414'])).

thf('416',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['408','415'])).

thf('417',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('418',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('419',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,
    ( ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['416','419'])).

thf('421',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('422',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['420','421'])).

thf('423',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['410','411'])).

thf('424',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['422','423'])).

thf('425',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('426',plain,
    ( ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['424','425'])).

thf('427',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['407','426'])).

thf('428',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['393','394'])).

thf('429',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('430',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('431',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['427','428','429','430'])).

thf('432',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('433',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X15 )
       != ( k2_struct_0 @ X16 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X15 )
       != ( k2_struct_0 @ X14 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v5_pre_topc @ X15 @ X16 @ X14 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X15 ) @ X14 @ X16 )
      | ( v3_tops_2 @ X15 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('435',plain,
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
    inference('sup-',[status(thm)],['433','434'])).

thf('436',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('437',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('438',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('440',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['435','436','437','438','439'])).

thf('441',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('442',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('443',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['440','441','442'])).

thf('444',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['432','443'])).

thf('445',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('446',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['444','445'])).

thf('447',plain,
    ( ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['446'])).

thf('448',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['431','447'])).

thf('449',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['393','394'])).

thf('450',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_B @ sk_A )
      | ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['448','449'])).

thf('451',plain,
    ( ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_B @ sk_A ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['450'])).

thf('452',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['406','451'])).

thf('453',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('454',plain,
    ( ( ~ ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['452','453'])).

thf('455',plain,
    ( ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['391','454'])).

thf('456',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_A ) )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) )
      & ( v2_funct_1 @ sk_C )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) )
      & ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ( v4_pre_topc @ X54 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['269','455'])).

thf('457',plain,
    ( ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('458',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['457'])).

thf('459',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ( v4_pre_topc @ X54 @ sk_A ) )
    | ~ ! [X54: $i] :
          ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
          | ~ ( v4_pre_topc @ X54 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['456','458'])).

thf('460',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ! [X54: $i] :
        ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X54 ) @ sk_B )
        | ~ ( v4_pre_topc @ X54 @ sk_A ) ) ),
    inference(split,[status(esa)],['97'])).

thf('461',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('462',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['336','341'])).

thf('463',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('464',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
      | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['462','463'])).

thf('465',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('466',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('467',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('468',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('469',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['467','468'])).

thf('470',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('471',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['469','470'])).

thf('472',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['466','471'])).

thf('473',plain,
    ( ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['464','465','472'])).

thf('474',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('475',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('476',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v5_pre_topc @ X7 @ X8 @ X6 )
      | ~ ( v4_pre_topc @ X9 @ X6 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) @ X7 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('477',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ X3 ) @ X0 )
      | ~ ( v4_pre_topc @ X3 @ X1 )
      | ~ ( v5_pre_topc @ X2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['475','476'])).

thf('478',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v4_pre_topc @ X2 @ X0 )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ X2 ) @ sk_B )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( l1_pre_topc @ sk_B )
        | ~ ( l1_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['474','477'])).

thf('479',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('480',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('481',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v4_pre_topc @ X2 @ X0 )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ X2 ) @ sk_B )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['478','479','480'])).

thf('482',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('483',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('484',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v5_pre_topc @ X1 @ sk_B @ X0 )
        | ~ ( v4_pre_topc @ X2 @ X0 )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ X2 ) @ sk_B )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
        | ~ ( v1_funct_1 @ X1 ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['481','482','483'])).

thf('485',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
        | ~ ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ X0 ) @ sk_B )
        | ~ ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_B @ sk_A )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['473','484'])).

thf('486',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('487',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('488',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('489',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('490',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('491',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['275','276','277'])).

thf('492',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( u1_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['490','491'])).

thf('493',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('494',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['492','493'])).

thf('495',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['489','494'])).

thf('496',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('497',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['495','496'])).

thf('498',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['497'])).

thf('499',plain,
    ( ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['488','498'])).

thf('500',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('501',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['499','500'])).

thf('502',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('503',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['501','502'])).

thf('504',plain,
    ( ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['487','503'])).

thf('505',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('506',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['504','505'])).

thf('507',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('508',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['506','507'])).

thf('509',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['497'])).

thf('510',plain,(
    v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('511',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['509','510'])).

thf('512',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('513',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['506','507'])).

thf('514',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('515',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('516',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('517',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['339','340'])).

thf('518',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X17 @ X18 @ X19 ) @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('519',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['517','518'])).

thf('520',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('521',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['469','470'])).

thf('522',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['519','520','521'])).

thf('523',plain,
    ( ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['516','522'])).

thf('524',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('525',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['523','524'])).

thf('526',plain,
    ( ( v1_funct_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['515','525'])).

thf('527',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('528',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['497'])).

thf('529',plain,
    ( ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['527','528'])).

thf('530',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('531',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['529','530'])).

thf('532',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['526','531'])).

thf('533',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('534',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['532','533'])).

thf('535',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('536',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('537',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('538',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['506','507'])).

thf('539',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('540',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('541',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('542',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['540','541'])).

thf('543',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('544',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['542','543'])).

thf('545',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['539','544'])).

thf('546',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('547',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['545','546'])).

thf('548',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('549',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('550',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('551',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('552',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('553',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['551','552'])).

thf('554',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('555',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['553','554'])).

thf('556',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['550','555'])).

thf('557',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('558',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['556','557'])).

thf('559',plain,
    ( ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['549','558'])).

thf('560',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('561',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['499','500'])).

thf('562',plain,
    ( ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['560','561'])).

thf('563',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('564',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['562','563'])).

thf('565',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('566',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['564','565'])).

thf('567',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['547','548','559','566'])).

thf('568',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('569',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['567','568'])).

thf('570',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k8_relset_1 @ X40 @ X41 @ X39 @ X42 )
        = ( k10_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('571',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['569','570'])).

thf('572',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('573',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['369','370'])).

thf('574',plain,
    ( ! [X0: $i] :
        ( ( k9_relat_1 @ sk_C @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['572','573'])).

thf('575',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k9_relat_1 @ sk_C @ X0 ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['571','574'])).

thf('576',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('577',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['506','507'])).

thf('578',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('579',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('580',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v3_tops_2 @ X15 @ X16 @ X14 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) @ X15 ) @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('581',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['579','580'])).

thf('582',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('583',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('584',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('585',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('586',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['581','582','583','584','585'])).

thf('587',plain,
    ( ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['578','586'])).

thf('588',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['497'])).

thf('589',plain,
    ( ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['587','588'])).

thf('590',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('591',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_C ) ) )
        | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['485','486','508','511','512','513','514','534','535','536','537','538','575','576','577','589','590'])).

thf('592',plain,
    ( ( ~ ( v4_pre_topc @ sk_D_1 @ sk_A )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['461','591'])).

thf('593',plain,
    ( ( v4_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['218'])).

thf('594',plain,
    ( ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['592','593'])).

thf('595',plain,
    ( ~ ( v4_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ sk_D_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('596',plain,
    ( ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      | ( ( k1_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v4_pre_topc @ sk_D_1 @ sk_A ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['594','595'])).

thf('597',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('598',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('599',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('600',plain,
    ( ( v2_funct_1 @ sk_C )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('601',plain,
    ( ( v4_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['218'])).

thf('602',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) ) )
   <= ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
      & ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
        = ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['596','597','598','599','600','601'])).

thf('603',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['602'])).

thf('604',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
   <= ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('605',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['457'])).

thf('606',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      & ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['604','605'])).

thf('607',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['606'])).

thf('608',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','221','459','460','603','607'])).


%------------------------------------------------------------------------------
