%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DA9kHUocK6

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 178 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  789 (4128 expanded)
%              Number of equality atoms :   43 ( 176 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

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

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
     != ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
     != ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X14 @ X16 )
       != X14 )
      | ~ ( v2_funct_1 @ X16 )
      | ( ( k2_tops_2 @ X15 @ X14 @ X16 )
        = ( k2_funct_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','21','22','27'])).

thf('29',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['8','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k8_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k10_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ( k10_relat_1 @ sk_C @ sk_D )
 != ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('40',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['28'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ( ( k7_relset_1 @ X6 @ X7 @ X5 @ X8 )
        = ( k9_relat_1 @ X5 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

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
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('54',plain,(
    ( k10_relat_1 @ sk_C @ sk_D )
 != ( k10_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['34','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DA9kHUocK6
% 0.14/0.36  % Computer   : n012.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:29:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 121 iterations in 0.052s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.53  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(d3_struct_0, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X13 : $i]:
% 0.22/0.53         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X13 : $i]:
% 0.22/0.53         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.53  thf(t68_tops_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_struct_0 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( l1_struct_0 @ B ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                 ( m1_subset_1 @
% 0.22/0.53                   C @ 
% 0.22/0.53                   ( k1_zfmisc_1 @
% 0.22/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.53                   ( ( ( ( k2_relset_1 @
% 0.22/0.53                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.22/0.53                         ( k2_struct_0 @ B ) ) & 
% 0.22/0.53                       ( v2_funct_1 @ C ) ) =>
% 0.22/0.53                     ( ( k8_relset_1 @
% 0.22/0.53                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.22/0.53                       ( k7_relset_1 @
% 0.22/0.53                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.53                         ( k2_tops_2 @
% 0.22/0.53                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.22/0.53                         D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( l1_struct_0 @ A ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( l1_struct_0 @ B ) =>
% 0.22/0.53              ( ![C:$i]:
% 0.22/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.53                    ( v1_funct_2 @
% 0.22/0.53                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                    ( m1_subset_1 @
% 0.22/0.53                      C @ 
% 0.22/0.53                      ( k1_zfmisc_1 @
% 0.22/0.53                        ( k2_zfmisc_1 @
% 0.22/0.53                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                  ( ![D:$i]:
% 0.22/0.53                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.53                      ( ( ( ( k2_relset_1 @
% 0.22/0.53                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.22/0.53                            ( k2_struct_0 @ B ) ) & 
% 0.22/0.53                          ( v2_funct_1 @ C ) ) =>
% 0.22/0.53                        ( ( k8_relset_1 @
% 0.22/0.53                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) =
% 0.22/0.53                          ( k7_relset_1 @
% 0.22/0.53                            ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.53                            ( k2_tops_2 @
% 0.22/0.53                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.22/0.53                            D ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t68_tops_2])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.53         sk_D)
% 0.22/0.53         != (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.22/0.53             sk_D))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.53          sk_D)
% 0.22/0.53          != (k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.22/0.53              sk_D))
% 0.22/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.53         sk_D)
% 0.22/0.53         != (k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.22/0.53             sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.53          sk_D)
% 0.22/0.53          != (k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.22/0.53              sk_D))
% 0.22/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.53  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.53         sk_D)
% 0.22/0.53         != (k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.22/0.53             sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X13 : $i]:
% 0.22/0.53         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (((m1_subset_1 @ sk_C @ 
% 0.22/0.53         (k1_zfmisc_1 @ 
% 0.22/0.53          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.22/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf(d4_tops_2, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.53       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.53         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.53         (((k2_relset_1 @ X15 @ X14 @ X16) != (X14))
% 0.22/0.53          | ~ (v2_funct_1 @ X16)
% 0.22/0.53          | ((k2_tops_2 @ X15 @ X14 @ X16) = (k2_funct_1 @ X16))
% 0.22/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.22/0.53          | ~ (v1_funct_2 @ X16 @ X15 @ X14)
% 0.22/0.53          | ~ (v1_funct_1 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      ((~ (v1_funct_1 @ sk_C)
% 0.22/0.53        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.53        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53            = (k2_funct_1 @ sk_C))
% 0.22/0.53        | ~ (v2_funct_1 @ sk_C)
% 0.22/0.53        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53            != (k2_struct_0 @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X13 : $i]:
% 0.22/0.53         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.53  thf('22', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X13 : $i]:
% 0.22/0.53         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53         = (k2_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53          = (k2_struct_0 @ sk_B))
% 0.22/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53         = (k2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53          = (k2_funct_1 @ sk_C))
% 0.22/0.53        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.22/0.53      inference('demod', [status(thm)], ['15', '16', '21', '22', '27'])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53         = (k2_funct_1 @ sk_C))),
% 0.22/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.53         sk_D)
% 0.22/0.53         != (k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53             (k2_funct_1 @ sk_C) @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['8', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.22/0.53          | ((k8_relset_1 @ X10 @ X11 @ X9 @ X12) = (k10_relat_1 @ X9 @ X12)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.53           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_C @ sk_D)
% 0.22/0.53         != (k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53             (k2_funct_1 @ sk_C) @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['30', '33'])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf(dt_k2_tops_2, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.53       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.22/0.53         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.22/0.53         ( m1_subset_1 @
% 0.22/0.53           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.22/0.53           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k2_tops_2 @ X17 @ X18 @ X19) @ 
% 0.22/0.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.53          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.22/0.53          | ~ (v1_funct_1 @ X19))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      ((~ (v1_funct_1 @ sk_C)
% 0.22/0.53        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.22/0.53        | (m1_subset_1 @ 
% 0.22/0.53           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.22/0.53           (k1_zfmisc_1 @ 
% 0.22/0.53            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.53         = (k2_funct_1 @ sk_C))),
% 0.22/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.22/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.22/0.53          | ((k7_relset_1 @ X6 @ X7 @ X5 @ X8) = (k9_relat_1 @ X5 @ X8)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53           (k2_funct_1 @ sk_C) @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.53  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t155_funct_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.53       ( ( v2_funct_1 @ B ) =>
% 0.22/0.53         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X0)
% 0.22/0.53          | ((k10_relat_1 @ X0 @ X1) = (k9_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.22/0.53          | ~ (v1_funct_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ sk_C)
% 0.22/0.53          | ((k10_relat_1 @ sk_C @ X0)
% 0.22/0.53              = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.22/0.53          | ~ (v2_funct_1 @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.53  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ sk_C)
% 0.22/0.53          | ((k10_relat_1 @ sk_C @ X0)
% 0.22/0.53              = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_C @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc1_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( v1_relat_1 @ C ) ))).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         ((v1_relat_1 @ X2)
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.53  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.53  thf('52', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k10_relat_1 @ sk_C @ X0) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['48', '51'])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k7_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.53           (k2_funct_1 @ sk_C) @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['43', '52'])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_C @ sk_D) != (k10_relat_1 @ sk_C @ sk_D))),
% 0.22/0.53      inference('demod', [status(thm)], ['34', '53'])).
% 0.22/0.53  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
