%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FB4ZcfMAc9

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 149 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  783 (3375 expanded)
%              Number of equality atoms :   45 ( 145 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ X1 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t67_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                        = ( k2_struct_0 @ B ) )
                      & ( v2_funct_1 @ C ) )
                   => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                      = ( k8_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) )).

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
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                          = ( k2_struct_0 @ B ) )
                        & ( v2_funct_1 @ C ) )
                     => ( ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                        = ( k8_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tops_2])).

thf('3',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( ( k7_relset_1 @ X6 @ X7 @ X5 @ X8 )
        = ( k9_relat_1 @ X5 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ sk_C @ sk_D )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_D )
     != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ( k9_relat_1 @ sk_C @ sk_D )
 != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_D )
     != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ( k9_relat_1 @ sk_C @ sk_D )
 != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X17 @ X19 )
       != X17 )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k2_tops_2 @ X18 @ X17 @ X19 )
        = ( k2_funct_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','26','27','32'])).

thf('34',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k9_relat_1 @ sk_C @ sk_D )
 != ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['13','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relset_1 @ X15 @ X14 @ X13 )
       != X14 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k8_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k10_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ( k9_relat_1 @ sk_C @ sk_D )
 != ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_D )
     != ( k9_relat_1 @ sk_C @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ( k9_relat_1 @ sk_C @ sk_D )
 != ( k9_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['48','51','52','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FB4ZcfMAc9
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 126 iterations in 0.044s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.19/0.49  thf(t154_funct_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.49       ( ( v2_funct_1 @ B ) =>
% 0.19/0.49         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (v2_funct_1 @ X0)
% 0.19/0.49          | ((k9_relat_1 @ X0 @ X1) = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.19/0.49          | ~ (v1_funct_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.19/0.49  thf(d3_struct_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X16 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X16 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf(t67_tops_2, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( l1_struct_0 @ B ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.49                 ( m1_subset_1 @
% 0.19/0.49                   C @ 
% 0.19/0.49                   ( k1_zfmisc_1 @
% 0.19/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49                   ( ( ( ( k2_relset_1 @
% 0.19/0.49                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.49                         ( k2_struct_0 @ B ) ) & 
% 0.19/0.49                       ( v2_funct_1 @ C ) ) =>
% 0.19/0.49                     ( ( k7_relset_1 @
% 0.19/0.49                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.19/0.49                       ( k8_relset_1 @
% 0.19/0.49                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.49                         ( k2_tops_2 @
% 0.19/0.49                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.19/0.49                         D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( l1_struct_0 @ A ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( l1_struct_0 @ B ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49                    ( v1_funct_2 @
% 0.19/0.49                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.49                    ( m1_subset_1 @
% 0.19/0.49                      C @ 
% 0.19/0.49                      ( k1_zfmisc_1 @
% 0.19/0.49                        ( k2_zfmisc_1 @
% 0.19/0.49                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.49                  ( ![D:$i]:
% 0.19/0.49                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.49                      ( ( ( ( k2_relset_1 @
% 0.19/0.49                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.49                            ( k2_struct_0 @ B ) ) & 
% 0.19/0.49                          ( v2_funct_1 @ C ) ) =>
% 0.19/0.49                        ( ( k7_relset_1 @
% 0.19/0.49                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.19/0.49                          ( k8_relset_1 @
% 0.19/0.49                            ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.49                            ( k2_tops_2 @
% 0.19/0.49                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.19/0.49                            D ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t67_tops_2])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.49         sk_D)
% 0.19/0.49         != (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.49             sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.19/0.49          | ((k7_relset_1 @ X6 @ X7 @ X5 @ X8) = (k9_relat_1 @ X5 @ X8)))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.19/0.49           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (((k9_relat_1 @ sk_C @ sk_D)
% 0.19/0.49         != (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.49             sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      ((((k9_relat_1 @ sk_C @ sk_D)
% 0.19/0.49          != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.49              sk_D))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '7'])).
% 0.19/0.49  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (((k9_relat_1 @ sk_C @ sk_D)
% 0.19/0.49         != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.49             sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((((k9_relat_1 @ sk_C @ sk_D)
% 0.19/0.49          != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.49              sk_D))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '10'])).
% 0.19/0.49  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (((k9_relat_1 @ sk_C @ sk_D)
% 0.19/0.49         != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.49             sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X16 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_C @ 
% 0.19/0.49         (k1_zfmisc_1 @ 
% 0.19/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf(d4_tops_2, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.49       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.19/0.49         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         (((k2_relset_1 @ X18 @ X17 @ X19) != (X17))
% 0.19/0.49          | ~ (v2_funct_1 @ X19)
% 0.19/0.49          | ((k2_tops_2 @ X18 @ X17 @ X19) = (k2_funct_1 @ X19))
% 0.19/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.19/0.49          | ~ (v1_funct_2 @ X19 @ X18 @ X17)
% 0.19/0.49          | ~ (v1_funct_1 @ X19))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.49        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.19/0.49        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49            = (k2_funct_1 @ sk_C))
% 0.19/0.49        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.49        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49            != (k2_struct_0 @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X16 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X16 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49         = (k2_struct_0 @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49          = (k2_struct_0 @ sk_B))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49         = (k2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49          = (k2_funct_1 @ sk_C))
% 0.19/0.49        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21', '26', '27', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49         = (k2_funct_1 @ sk_C))),
% 0.19/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (((k9_relat_1 @ sk_C @ sk_D)
% 0.19/0.49         != (k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49             (k2_funct_1 @ sk_C) @ sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf(t31_funct_2, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.49       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.19/0.49         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.19/0.49           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.19/0.49           ( m1_subset_1 @
% 0.19/0.49             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (v2_funct_1 @ X13)
% 0.19/0.49          | ((k2_relset_1 @ X15 @ X14 @ X13) != (X14))
% 0.19/0.49          | (m1_subset_1 @ (k2_funct_1 @ X13) @ 
% 0.19/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.19/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.19/0.49          | ~ (v1_funct_2 @ X13 @ X15 @ X14)
% 0.19/0.49          | ~ (v1_funct_1 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.49        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.19/0.49        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.49           (k1_zfmisc_1 @ 
% 0.19/0.49            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.19/0.49        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49            != (k2_struct_0 @ sk_B))
% 0.19/0.49        | ~ (v2_funct_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.19/0.49         = (k2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.49         (k1_zfmisc_1 @ 
% 0.19/0.49          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.19/0.49        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.19/0.49          | ((k8_relset_1 @ X10 @ X11 @ X9 @ X12) = (k10_relat_1 @ X9 @ X12)))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k8_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49           (k2_funct_1 @ sk_C) @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (((k9_relat_1 @ sk_C @ sk_D)
% 0.19/0.49         != (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['35', '46'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      ((((k9_relat_1 @ sk_C @ sk_D) != (k9_relat_1 @ sk_C @ sk_D))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.49        | ~ (v2_funct_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc1_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( v1_relat_1 @ C ) ))).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         ((v1_relat_1 @ X2)
% 0.19/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.49  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.50      (((k9_relat_1 @ sk_C @ sk_D) != (k9_relat_1 @ sk_C @ sk_D))),
% 0.19/0.50      inference('demod', [status(thm)], ['48', '51', '52', '53'])).
% 0.19/0.50  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
