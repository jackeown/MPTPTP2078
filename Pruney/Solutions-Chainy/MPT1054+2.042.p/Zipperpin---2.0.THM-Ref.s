%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cXMH8MknE3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 237 expanded)
%              Number of leaves         :   36 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  636 (1492 expanded)
%              Number of equality atoms :   58 ( 148 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X18: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X18 ) @ X18 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('6',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('12',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf(t171_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_2])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('23',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X16 ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_B ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k10_relat_1 @ X6 @ ( k10_relat_1 @ X5 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X26 ) )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('31',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X26: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X26 ) )
      = ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k10_relat_1 @ X24 @ X25 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X24 ) @ X25 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X21 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('41',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36','39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k10_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36','39','42'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36','39','42'])).

thf('50',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
      = ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k9_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_B )
    = ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['15','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf('54',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('56',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('57',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36','39','42'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ( k9_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cXMH8MknE3
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 57 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(fc24_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.49       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('0', plain, (![X18 : $i]: (v4_relat_1 @ (k6_relat_1 @ X18) @ X18)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.49  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.49  thf('1', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('2', plain, (![X18 : $i]: (v4_relat_1 @ (k6_partfun1 @ X18) @ X18)),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t209_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.20/0.49          | ~ (v4_relat_1 @ X8 @ X9)
% 0.20/0.49          | ~ (v1_relat_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.49          | ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.49  thf('6', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('7', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '7'])).
% 0.20/0.49  thf(t148_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.49            = (k9_relat_1 @ (k6_partfun1 @ X0) @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(t71_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('11', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf('12', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('13', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.20/0.49  thf(t171_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49          ( ( k8_relset_1 @ A @ A @ ( k6_partfun1 @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t171_funct_2])).
% 0.20/0.49  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('18', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf('20', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('21', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf(t77_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.49         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.20/0.49          | ((k5_relat_1 @ (k6_relat_1 @ X16) @ X15) = (X15))
% 0.20/0.49          | ~ (v1_relat_1 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.20/0.49  thf('23', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.20/0.49          | ((k5_relat_1 @ (k6_partfun1 @ X16) @ X15) = (X15))
% 0.20/0.49          | ~ (v1_relat_1 @ X15))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.49          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 0.20/0.49              = (k6_partfun1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.49  thf('26', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.49          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 0.20/0.49              = (k6_partfun1 @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k6_partfun1 @ sk_B))
% 0.20/0.49         = (k6_partfun1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '27'])).
% 0.20/0.49  thf(t181_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ C ) =>
% 0.20/0.49           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.49             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ((k10_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.20/0.49              = (k10_relat_1 @ X6 @ (k10_relat_1 @ X5 @ X7)))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.20/0.49  thf(t67_funct_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X26 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X26)) = (k6_relat_1 @ X26))),
% 0.20/0.49      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.20/0.49  thf('31', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('32', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X26 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X26)) = (k6_partfun1 @ X26))),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.49  thf(t155_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( v2_funct_1 @ B ) =>
% 0.20/0.49         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (v2_funct_1 @ X24)
% 0.20/0.49          | ((k10_relat_1 @ X24 @ X25)
% 0.20/0.49              = (k9_relat_1 @ (k2_funct_1 @ X24) @ X25))
% 0.20/0.49          | ~ (v1_funct_1 @ X24)
% 0.20/0.49          | ~ (v1_relat_1 @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.49            = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.20/0.49          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(fc3_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('37', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('38', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('39', plain, (![X21 : $i]: (v1_funct_1 @ (k6_partfun1 @ X21))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf(fc4_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('40', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.50  thf('41', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('42', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 0.20/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36', '39', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k10_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X2) @ X1) @ X0)
% 0.20/0.50            = (k9_relat_1 @ (k6_partfun1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ X2))
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['29', '43'])).
% 0.20/0.50  thf('45', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k10_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X2) @ X1) @ X0)
% 0.20/0.50            = (k9_relat_1 @ (k6_partfun1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k10_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.20/0.50            = (k9_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.50               (k10_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['28', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36', '39', '42'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36', '39', '42'])).
% 0.20/0.50  thf('50', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k9_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.20/0.50           = (k9_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.50              (k9_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (((k9_relat_1 @ (k6_partfun1 @ sk_B) @ sk_B)
% 0.20/0.50         = (k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.20/0.50  thf('54', plain, (((sk_B) = (k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (((k8_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t29_relset_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( m1_subset_1 @
% 0.20/0.50       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X31 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.20/0.50  thf('57', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X31 : $i]:
% 0.20/0.50         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.20/0.50          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.20/0.50      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.20/0.50          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k10_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k10_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36', '39', '42'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k8_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.20/0.50           = (k9_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain, (((k9_relat_1 @ (k6_partfun1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '62'])).
% 0.20/0.50  thf('64', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['54', '63'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
