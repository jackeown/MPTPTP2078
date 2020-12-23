%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HajFnNHjtd

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 289 expanded)
%              Number of leaves         :   38 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  976 (3665 expanded)
%              Number of equality atoms :   76 ( 209 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k8_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k10_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['11','16'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

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
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    inference(demod,[status(thm)],['14','15'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['14','15'])).

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
    inference(demod,[status(thm)],['14','15'])).

thf('75',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HajFnNHjtd
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 63 iterations in 0.036s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.55  thf(t146_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X7 : $i]:
% 0.21/0.55         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.21/0.55          | ~ (v1_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.55  thf(t39_relset_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.55       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.55           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.55         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.55           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.55          ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.55              ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.55            ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.55              ( k1_relset_1 @ B @ A @ C ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t39_relset_1])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.21/0.55          | ((k8_relset_1 @ X33 @ X34 @ X32 @ X35) = (k10_relat_1 @ X32 @ X35)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.55          != (k2_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.21/0.55        | ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55            (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55            != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.55          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.55                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((((k7_relset_1 @ sk_B @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.55          != (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.55                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.55         ((v5_relat_1 @ X19 @ X21)
% 0.21/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.55  thf('9', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.55  thf(d19_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (v5_relat_1 @ X2 @ X3)
% 0.21/0.55          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.21/0.55          | ~ (v1_relat_1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.55          | (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf(fc6_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.55  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.55  thf(t79_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.55         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.21/0.55          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 0.21/0.55          | ~ (v1_relat_1 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('21', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_A)) = (sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf(t71_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.55  thf('22', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf(t182_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( v1_relat_1 @ B ) =>
% 0.21/0.55           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.55             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X11)
% 0.21/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.21/0.55              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 0.21/0.55          | ~ (v1_relat_1 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.55  thf('25', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['21', '26'])).
% 0.21/0.55  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('29', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.21/0.55          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.55         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.21/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.55                = (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '29', '32', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k8_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.55          != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.55         ((v4_relat_1 @ X19 @ X20)
% 0.21/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.55  thf('43', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.55  thf(t209_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i]:
% 0.21/0.55         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.21/0.55          | ~ (v4_relat_1 @ X13 @ X14)
% 0.21/0.55          | ~ (v1_relat_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.55  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('47', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf(t148_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.21/0.55          | ~ (v1_relat_1 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('51', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.55         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.21/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ (k2_relat_1 @ sk_C))
% 0.21/0.55          != (k1_relat_1 @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['40', '51', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['37', '55'])).
% 0.21/0.55  thf('57', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('58', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.21/0.55          | ~ (v1_relat_1 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.55  thf(t169_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X10 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.55            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['58', '59'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ 
% 0.21/0.55            (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.55            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['57', '60'])).
% 0.21/0.55  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('64', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('65', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('66', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['61', '62', '63', '64', '65', '66'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55                (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55                = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.21/0.55      inference('demod', [status(thm)], ['56', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      (~
% 0.21/0.55       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.55          = (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.21/0.55       ~
% 0.21/0.55       (((k8_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55          (k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 0.21/0.55          = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (~
% 0.21/0.55       (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ 
% 0.21/0.55          (k8_relset_1 @ sk_B @ sk_A @ sk_C @ sk_A))
% 0.21/0.55          = (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['36', '71'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '72'])).
% 0.21/0.55  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('75', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.55  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
