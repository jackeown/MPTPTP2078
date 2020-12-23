%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cYVFUA0hbF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 253 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  981 (3510 expanded)
%              Number of equality atoms :   76 ( 209 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['11','14'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['17','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
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

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('23',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','29','32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('39',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('40',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('47',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','51','54'])).

thf('56',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','55'])).

thf('57',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('64',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('66',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('67',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66'])).

thf('68',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','67'])).

thf('69',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
     != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('71',plain,(
    ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ ( k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A ) )
 != ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['36','71'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('75',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cYVFUA0hbF
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 78 iterations in 0.050s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(t146_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X2 : $i]:
% 0.21/0.51         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 0.21/0.51          | ~ (v1_relat_1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.51  thf(t39_relset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.51       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.51           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.51         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.51           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.51          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.51              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.51            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.51              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.51          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.51        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.51          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X17 @ X19)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('9', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(d19_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v5_relat_1 @ X0 @ X1)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.51  thf(t79_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.51         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.21/0.51          | ((k5_relat_1 @ X12 @ (k6_relat_1 @ X13)) = (X12))
% 0.21/0.51          | ~ (v1_relat_1 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.51        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('19', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf(t71_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('20', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf(t182_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.51             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X6)
% 0.21/0.51          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.21/0.51              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf(t29_relset_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( m1_subset_1 @
% 0.21/0.51       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X34 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.21/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('25', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X1))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '26'])).
% 0.21/0.51  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('29', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.21/0.51          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.51         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '29', '32', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.51          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X17 @ X18)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('43', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf(t209_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.21/0.51          | ~ (v4_relat_1 @ X8 @ X9)
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('47', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf(t148_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('51', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.21/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.51          != (k1_relat_1 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '51', '54'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '55'])).
% 0.21/0.51  thf('57', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf(t169_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X5 : $i]:
% 0.21/0.51         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.21/0.51          | ~ (v1_relat_1 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.51            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.51        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.21/0.51            (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.51            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '60'])).
% 0.21/0.51  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('64', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('65', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('66', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['61', '62', '63', '64', '65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['56', '67'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (~
% 0.21/0.51       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.21/0.51       ~
% 0.21/0.51       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.51          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (~
% 0.21/0.51       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.51          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.51          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['36', '71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '72'])).
% 0.21/0.51  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('75', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
