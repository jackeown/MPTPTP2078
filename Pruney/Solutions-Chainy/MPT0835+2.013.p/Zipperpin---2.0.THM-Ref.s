%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.akMK1alLgO

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 265 expanded)
%              Number of leaves         :   37 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          : 1091 (3739 expanded)
%              Number of equality atoms :   85 ( 230 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t39_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
            = ( k2_relset_1 @ B @ A @ C ) )
          & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
            = ( k1_relset_1 @ B @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('15',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','29','32'])).

thf('34',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','33'])).

thf('35',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('44',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('52',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('53',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','55'])).

thf('57',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('59',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['12','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('62',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k8_relset_1 @ X38 @ X39 @ X40 @ X39 )
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('63',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('66',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('69',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('73',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('77',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','66','81'])).

thf('83',plain,(
    $false ),
    inference(simplify,[status(thm)],['82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.akMK1alLgO
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 107 iterations in 0.065s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.52  thf(t39_relset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.52       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.20/0.52           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.52         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.20/0.52           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.52          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.20/0.52              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.52            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.20/0.52              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.20/0.52          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.20/0.52        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.20/0.52          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.20/0.52          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.20/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.20/0.52          != (k2_relat_1 @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.52                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '8', '11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.20/0.52          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         ((v4_relat_1 @ X17 @ X18)
% 0.20/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.52  thf('19', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf(t209_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.20/0.52          | ~ (v4_relat_1 @ X8 @ X9)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( v1_relat_1 @ C ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         ((v1_relat_1 @ X14)
% 0.20/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.52  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.52  thf(t148_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.52          | ~ (v1_relat_1 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('29', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.20/0.52          != (k1_relat_1 @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '29', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '33'])).
% 0.20/0.52  thf('35', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.52          | ~ (v1_relat_1 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.52  thf(t79_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.52         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.20/0.52          | ((k5_relat_1 @ X12 @ (k6_relat_1 @ X13)) = (X12))
% 0.20/0.52          | ~ (v1_relat_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf(t71_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.52  thf('41', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.52  thf(t182_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( v1_relat_1 @ B ) =>
% 0.20/0.52           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.52             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X6)
% 0.20/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.20/0.52              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.20/0.52          | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.52  thf('44', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.20/0.52          | ~ (v1_relat_1 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['40', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.52            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['36', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.20/0.52            = (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.20/0.52               (k9_relat_1 @ sk_C @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '48'])).
% 0.20/0.52  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('52', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.52  thf('53', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.52  thf('54', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (~
% 0.20/0.52       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.52          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.52       ~
% 0.20/0.52       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.20/0.52          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.52      inference('split', [status(esa)], ['3'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (~
% 0.20/0.52       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.20/0.52          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.20/0.52          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.20/0.52         != (k2_relat_1 @ sk_C))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['12', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t38_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.52         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.52         (((k8_relset_1 @ X38 @ X39 @ X40 @ X39)
% 0.20/0.52            = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.20/0.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.20/0.52         = (k1_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('66', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.52  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.52      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t13_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.52       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.20/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.52         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 0.20/0.52          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.20/0.52          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.20/0.52      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.20/0.52          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['67', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         ((v4_relat_1 @ X17 @ X18)
% 0.20/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.52  thf('73', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.20/0.52          | ~ (v4_relat_1 @ X8 @ X9)
% 0.20/0.52          | ~ (v1_relat_1 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('77', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.52          | ~ (v1_relat_1 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup+', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.20/0.52      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['60', '66', '81'])).
% 0.20/0.52  thf('83', plain, ($false), inference('simplify', [status(thm)], ['82'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
