%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qdDZkOXGWv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:28 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 485 expanded)
%              Number of leaves         :   32 ( 157 expanded)
%              Depth                    :   23
%              Number of atoms          : 1831 (12606 expanded)
%              Number of equality atoms :   95 ( 519 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t68_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                          = ( k2_struct_0 @ B ) )
                        & ( v2_funct_1 @ C ) )
                     => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                        = ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_tops_2])).

thf('2',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
     != ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k10_relat_1 @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X19 @ X21 )
       != X19 )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_tops_2 @ X20 @ X19 @ X21 )
        = ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','22','23','28'])).

thf('30',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ( k10_relat_1 @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_D )
     != ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

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

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X17 @ X16 @ X15 )
       != X16 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('38',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k7_relset_1 @ X8 @ X9 @ X7 @ X10 )
        = ( k9_relat_1 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ( k10_relat_1 @ sk_C @ sk_D )
 != ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['32','43','44'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('46',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('47',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X17 @ X16 @ X15 )
       != X16 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('53',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('54',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('58',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('59',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('60',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('61',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('62',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('63',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k9_relat_1 @ X4 @ X5 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X4 ) @ X5 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','77'])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','79','84','85'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X25 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) @ X27 )
       != ( k2_struct_0 @ X25 ) )
      | ~ ( v2_funct_1 @ X27 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('89',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X19 @ X21 )
       != X19 )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_tops_2 @ X20 @ X19 @ X21 )
        = ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','105','106','107','108'])).

thf('110',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('115',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['86','110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['47','116'])).

thf('118',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('119',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('120',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k10_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['46','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ( k10_relat_1 @ sk_C @ sk_D )
 != ( k10_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['45','126'])).

thf('128',plain,(
    $false ),
    inference(simplify,[status(thm)],['127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qdDZkOXGWv
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 293 iterations in 0.153s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.57  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.36/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.57  thf(d3_struct_0, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (![X18 : $i]:
% 0.36/0.57         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (![X18 : $i]:
% 0.36/0.57         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.57  thf(t68_tops_2, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_struct_0 @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( l1_struct_0 @ B ) =>
% 0.36/0.57           ( ![C:$i]:
% 0.36/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.57                 ( m1_subset_1 @
% 0.36/0.57                   C @ 
% 0.36/0.57                   ( k1_zfmisc_1 @
% 0.36/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.57               ( ![D:$i]:
% 0.36/0.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.57                   ( ( ( ( k2_relset_1 @
% 0.36/0.57                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.57                         ( k2_struct_0 @ B ) ) & 
% 0.36/0.57                       ( v2_funct_1 @ C ) ) =>
% 0.36/0.57                     ( ( k8_relset_1 @
% 0.36/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.36/0.57                       ( k7_relset_1 @
% 0.36/0.57                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.57                         ( k2_tops_2 @
% 0.36/0.57                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.36/0.57                         D ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( l1_struct_0 @ A ) =>
% 0.36/0.57          ( ![B:$i]:
% 0.36/0.57            ( ( l1_struct_0 @ B ) =>
% 0.36/0.57              ( ![C:$i]:
% 0.36/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.57                    ( v1_funct_2 @
% 0.36/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.57                    ( m1_subset_1 @
% 0.36/0.57                      C @ 
% 0.36/0.57                      ( k1_zfmisc_1 @
% 0.36/0.57                        ( k2_zfmisc_1 @
% 0.36/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.57                  ( ![D:$i]:
% 0.36/0.57                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.57                      ( ( ( ( k2_relset_1 @
% 0.36/0.57                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.57                            ( k2_struct_0 @ B ) ) & 
% 0.36/0.57                          ( v2_funct_1 @ C ) ) =>
% 0.36/0.57                        ( ( k8_relset_1 @
% 0.36/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.36/0.57                          ( k7_relset_1 @
% 0.36/0.57                            ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.57                            ( k2_tops_2 @
% 0.36/0.57                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.36/0.57                            D ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t68_tops_2])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.57         sk_D)
% 0.36/0.57         != (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.57             sk_D))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.57          sk_D)
% 0.36/0.57          != (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.57              sk_D))
% 0.36/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.57  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.57         sk_D)
% 0.36/0.57         != (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.57             sk_D))),
% 0.36/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C @ 
% 0.36/0.57        (k1_zfmisc_1 @ 
% 0.36/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k8_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.36/0.57          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.57           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (((k10_relat_1 @ sk_C @ sk_D)
% 0.36/0.57         != (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.57             sk_D))),
% 0.36/0.57      inference('demod', [status(thm)], ['5', '8'])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X18 : $i]:
% 0.36/0.57         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C @ 
% 0.36/0.57        (k1_zfmisc_1 @ 
% 0.36/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_C @ 
% 0.36/0.57         (k1_zfmisc_1 @ 
% 0.36/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C @ 
% 0.36/0.57        (k1_zfmisc_1 @ 
% 0.36/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.57  thf(d4_tops_2, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.57         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.57         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.36/0.57          | ~ (v2_funct_1 @ X21)
% 0.36/0.57          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.36/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.36/0.57          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.36/0.57          | ~ (v1_funct_1 @ X21))),
% 0.36/0.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57            = (k2_funct_1 @ sk_C))
% 0.36/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57            != (k2_struct_0 @ sk_B)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      (![X18 : $i]:
% 0.36/0.57         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.57  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('23', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      (![X18 : $i]:
% 0.36/0.57         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57         = (k2_struct_0 @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('26', plain,
% 0.36/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57          = (k2_struct_0 @ sk_B))
% 0.36/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.57  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57         = (k2_struct_0 @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57          = (k2_funct_1 @ sk_C))
% 0.36/0.57        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['16', '17', '22', '23', '28'])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57         = (k2_funct_1 @ sk_C))),
% 0.36/0.57      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (((k10_relat_1 @ sk_C @ sk_D)
% 0.36/0.57         != (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57             (k2_funct_1 @ sk_C) @ sk_D))),
% 0.36/0.57      inference('demod', [status(thm)], ['9', '30'])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      ((((k10_relat_1 @ sk_C @ sk_D)
% 0.36/0.57          != (k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57              (k2_funct_1 @ sk_C) @ sk_D))
% 0.36/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['0', '31'])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C @ 
% 0.36/0.57        (k1_zfmisc_1 @ 
% 0.36/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.57  thf(t31_funct_2, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.57       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.36/0.57         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.36/0.57           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.36/0.57           ( m1_subset_1 @
% 0.36/0.57             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X15)
% 0.36/0.57          | ((k2_relset_1 @ X17 @ X16 @ X15) != (X16))
% 0.36/0.57          | (m1_subset_1 @ (k2_funct_1 @ X15) @ 
% 0.36/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.36/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.36/0.57          | ~ (v1_funct_2 @ X15 @ X17 @ X16)
% 0.36/0.57          | ~ (v1_funct_1 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.57        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.57           (k1_zfmisc_1 @ 
% 0.36/0.57            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.36/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57            != (k2_struct_0 @ sk_B))
% 0.36/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.57  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57         = (k2_struct_0 @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.57  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.57         (k1_zfmisc_1 @ 
% 0.36/0.57          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.36/0.57        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.36/0.57  thf('41', plain,
% 0.36/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.57        (k1_zfmisc_1 @ 
% 0.36/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.57      inference('simplify', [status(thm)], ['40'])).
% 0.36/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.36/0.57  thf('42', plain,
% 0.36/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.36/0.57          | ((k7_relset_1 @ X8 @ X9 @ X7 @ X10) = (k9_relat_1 @ X7 @ X10)))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.57           (k2_funct_1 @ sk_C) @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.57  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (((k10_relat_1 @ sk_C @ sk_D)
% 0.36/0.57         != (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_D))),
% 0.36/0.57      inference('demod', [status(thm)], ['32', '43', '44'])).
% 0.36/0.57  thf(t65_funct_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C @ 
% 0.36/0.57        (k1_zfmisc_1 @ 
% 0.36/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X15)
% 0.36/0.57          | ((k2_relset_1 @ X17 @ X16 @ X15) != (X16))
% 0.36/0.57          | (v1_funct_1 @ (k2_funct_1 @ X15))
% 0.36/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.36/0.57          | ~ (v1_funct_2 @ X15 @ X17 @ X16)
% 0.36/0.57          | ~ (v1_funct_1 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.57        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57            != (k2_struct_0 @ sk_B))
% 0.36/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.57  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.57         = (k2_struct_0 @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.57  thf('54', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.57        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.36/0.57  thf('56', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.36/0.57  thf('57', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('59', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('61', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('62', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      (![X6 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X6)
% 0.36/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.36/0.57          | ~ (v1_funct_1 @ X6)
% 0.36/0.57          | ~ (v1_relat_1 @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.57  thf(t154_funct_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.57       ( ( v2_funct_1 @ B ) =>
% 0.36/0.57         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      (![X4 : $i, X5 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X4)
% 0.36/0.57          | ((k9_relat_1 @ X4 @ X5) = (k10_relat_1 @ (k2_funct_1 @ X4) @ X5))
% 0.36/0.57          | ~ (v1_funct_1 @ X4)
% 0.36/0.57          | ~ (v1_relat_1 @ X4))),
% 0.36/0.57      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.36/0.57  thf('65', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['63', '64'])).
% 0.36/0.57  thf('66', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)
% 0.36/0.57              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['62', '65'])).
% 0.36/0.57  thf('67', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)
% 0.36/0.57            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['66'])).
% 0.36/0.57  thf('68', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)
% 0.36/0.57              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['61', '67'])).
% 0.36/0.57  thf('69', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)
% 0.36/0.57            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['68'])).
% 0.36/0.57  thf('70', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)
% 0.36/0.57              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['60', '69'])).
% 0.36/0.57  thf('71', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)
% 0.36/0.57            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['70'])).
% 0.36/0.57  thf('72', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ X0)
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.57          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X1)
% 0.36/0.57              = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['59', '71'])).
% 0.36/0.57  thf('73', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X1)
% 0.36/0.57            = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1))
% 0.36/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v2_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['72'])).
% 0.36/0.58  thf('74', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v2_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v2_funct_1 @ X0)
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.58          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X1)
% 0.36/0.58              = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['58', '73'])).
% 0.36/0.58  thf('75', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X1)
% 0.36/0.58            = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1))
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v2_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['74'])).
% 0.36/0.58  thf('76', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v2_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v2_funct_1 @ X0)
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X1)
% 0.36/0.58              = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['57', '75'])).
% 0.36/0.58  thf('77', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X1)
% 0.36/0.58            = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1))
% 0.36/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v2_funct_1 @ X0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['76'])).
% 0.36/0.58  thf('78', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ sk_C)
% 0.36/0.58          | ~ (v1_relat_1 @ sk_C)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.58          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 0.36/0.58              X0) = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['56', '77'])).
% 0.36/0.58  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('80', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(cc2_relat_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.58  thf('81', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.58          | (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.58  thf('82', plain,
% 0.36/0.58      ((~ (v1_relat_1 @ 
% 0.36/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.36/0.58        | (v1_relat_1 @ sk_C))),
% 0.36/0.58      inference('sup-', [status(thm)], ['80', '81'])).
% 0.36/0.58  thf(fc6_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.58  thf('83', plain,
% 0.36/0.58      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.58  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.58      inference('demod', [status(thm)], ['82', '83'])).
% 0.36/0.58  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('86', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.58          | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 0.36/0.58              X0) = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['78', '79', '84', '85'])).
% 0.36/0.58  thf('87', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t63_tops_2, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_struct_0 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( l1_struct_0 @ B ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.58                 ( m1_subset_1 @
% 0.36/0.58                   C @ 
% 0.36/0.58                   ( k1_zfmisc_1 @
% 0.36/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.58               ( ( ( ( k2_relset_1 @
% 0.36/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.36/0.58                 ( v2_funct_1 @
% 0.36/0.58                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf('88', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.58         (~ (l1_struct_0 @ X25)
% 0.36/0.58          | ((k2_relset_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27)
% 0.36/0.58              != (k2_struct_0 @ X25))
% 0.36/0.58          | ~ (v2_funct_1 @ X27)
% 0.36/0.58          | (v2_funct_1 @ 
% 0.36/0.58             (k2_tops_2 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27))
% 0.36/0.58          | ~ (m1_subset_1 @ X27 @ 
% 0.36/0.58               (k1_zfmisc_1 @ 
% 0.36/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.36/0.58          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.36/0.58          | ~ (v1_funct_1 @ X27)
% 0.36/0.58          | ~ (l1_struct_0 @ X26))),
% 0.36/0.58      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.36/0.58  thf('89', plain,
% 0.36/0.58      ((~ (l1_struct_0 @ sk_A)
% 0.36/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.58        | (v2_funct_1 @ 
% 0.36/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            != (k2_struct_0 @ sk_B))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['87', '88'])).
% 0.36/0.58  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('92', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('93', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('94', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('95', plain,
% 0.36/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.58         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.36/0.58          | ~ (v2_funct_1 @ X21)
% 0.36/0.58          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.36/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.36/0.58          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.36/0.58          | ~ (v1_funct_1 @ X21))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.58  thf('96', plain,
% 0.36/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            = (k2_funct_1 @ sk_C))
% 0.36/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            != (u1_struct_0 @ sk_B)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.36/0.58  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('98', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('100', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('101', plain,
% 0.36/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58          = (k2_funct_1 @ sk_C))
% 0.36/0.58        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.36/0.58  thf('102', plain,
% 0.36/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            = (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['93', '101'])).
% 0.36/0.58  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('104', plain,
% 0.36/0.58      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.36/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            = (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.36/0.58  thf('105', plain,
% 0.36/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('simplify', [status(thm)], ['104'])).
% 0.36/0.58  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('107', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('109', plain,
% 0.36/0.58      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.58        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)],
% 0.36/0.58                ['89', '90', '91', '92', '105', '106', '107', '108'])).
% 0.36/0.58  thf('110', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('simplify', [status(thm)], ['109'])).
% 0.36/0.58  thf('111', plain,
% 0.36/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['40'])).
% 0.36/0.58  thf('112', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.58          | (v1_relat_1 @ X0)
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.58  thf('113', plain,
% 0.36/0.58      ((~ (v1_relat_1 @ 
% 0.36/0.58           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.36/0.58        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['111', '112'])).
% 0.36/0.58  thf('114', plain,
% 0.36/0.58      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.58  thf('115', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('demod', [status(thm)], ['113', '114'])).
% 0.36/0.58  thf('116', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ X0)
% 0.36/0.58           = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['86', '110', '115'])).
% 0.36/0.58  thf('117', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.36/0.58            = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['47', '116'])).
% 0.36/0.58  thf('118', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('demod', [status(thm)], ['113', '114'])).
% 0.36/0.58  thf('119', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.36/0.58  thf('120', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('simplify', [status(thm)], ['109'])).
% 0.36/0.58  thf('121', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.36/0.58           = (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.36/0.58  thf('122', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0) = (k10_relat_1 @ sk_C @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ sk_C)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.58          | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.58      inference('sup+', [status(thm)], ['46', '121'])).
% 0.36/0.58  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.58      inference('demod', [status(thm)], ['82', '83'])).
% 0.36/0.58  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('126', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 0.36/0.58  thf('127', plain,
% 0.36/0.58      (((k10_relat_1 @ sk_C @ sk_D) != (k10_relat_1 @ sk_C @ sk_D))),
% 0.36/0.58      inference('demod', [status(thm)], ['45', '126'])).
% 0.36/0.58  thf('128', plain, ($false), inference('simplify', [status(thm)], ['127'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
